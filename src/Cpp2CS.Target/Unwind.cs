using System.Buffers.Binary;
using System.Collections.Immutable;
using Cpp2CS.Input;

namespace Cpp2CS.Target;

public readonly record struct Frame(ulong Start, ulong End, ulong Lsda);
public readonly record struct UnwindClause(long Selector, ulong TypeInfo);
public readonly record struct CallSite(ulong Start, ulong End, ulong Landing, ImmutableArray<UnwindClause> Clauses,
    bool Cleanup, bool Specification);

/// <summary>LSB .eh_frame 的 CIE/FDE 及 Itanium 异常 ABI 的调用点表。地址为链接虚拟地址。</summary>
public sealed class UnwindIndex
{
    readonly Frame[] frames;
    readonly ulong[] tables;
    public ReadOnlySpan<Frame> Frames => frames;
    readonly byte[] file;
    readonly Elf64 elf;
    readonly ElfSection? exceptions;

    ref struct Cursor(ReadOnlySpan<byte> source, ulong address)
    {
        readonly ReadOnlySpan<byte> data = source;
        public int At;
        public ulong Pc => checked(address + (uint)At);
        public byte Byte() => (uint)At < (uint)data.Length ? data[At++] : throw new InvalidDataException("展开表记录超出表尾");
        public uint Word()
        {
            if ((uint)At > data.Length || data.Length - At < 4) throw new InvalidDataException("展开表记录超出表尾");
            uint value = BinaryPrimitives.ReadUInt32LittleEndian(data[At..]);
            At += 4;
            return value;
        }
        public ulong Leb(bool signed = false)
        {
            ulong value = 0;
            for (int shift = 0; shift < 64; shift += 7)
            {
                byte b = Byte();
                if (shift == 63 && b != 0 && b != (signed ? 127 : 1)) throw new InvalidDataException("LEB128 超出 64 位");
                value |= (ulong)(b & 127) << shift;
                if (b < 128)
                    return signed && (b & 64) != 0 && shift < 57 ? value | (ulong.MaxValue << (shift + 7)) : value;
            }
            throw new InvalidDataException("LEB128 超出 64 位");
        }
        public ulong Encoded(int enc)
        {
            ulong origin = (enc & 0x70) switch { 0 => 0ul, 0x10 => Pc, _ => throw new InvalidDataException("未知 DW_EH_PE 基址") };
            ulong raw = (enc & 15) switch
            {
                1 => Leb(),
                9 => Leb(true),
                3 => Word(),
                11 => (ulong)(long)(int)Word(),
                0 or 4 or 12 => Word() | (ulong)Word() << 32,
                2 => (uint)(Byte() | Byte() << 8),
                10 => (ulong)(long)(short)(Byte() | Byte() << 8),
                _ => throw new InvalidDataException("未知 DW_EH_PE 位宽")
            };
            return raw == 0 ? 0 : unchecked(origin + raw);
        }
    }

    public UnwindIndex(Elf64 elf, byte[] file)
    {
        this.file = file;
        this.elf = elf;
        exceptions = elf.Sections.SingleOrDefault(s => s.Name == ".gcc_except_table");
        var section = elf.Sections.SingleOrDefault(s => s.Name == ".eh_frame");
        var ranges = new List<Frame>();
        var cies = new Dictionary<int, (int Pointer, int Lsda, bool Augmented)>();
        if (section != null)
        {
            var bytes = file.AsSpan((int)section.Offset, (int)section.Size);
            for (int at = 0; at < bytes.Length;)
            {
                var head = new Cursor(bytes[at..], section.Address + (uint)at);
                int length = checked((int)head.Word());
                if (length == 0) break;
                var row = new Cursor(bytes.Slice(at + 4, length), section.Address + (uint)at + 4);
                int id = checked((int)row.Word());
                if (id == 0)
                {
                    int version = row.Byte();
                    if (version is not (1 or 3)) throw new InvalidDataException("未知 CIE 版本");
                    int first = row.At;
                    while (row.Byte() != 0) { }
                    string aug = System.Text.Encoding.ASCII.GetString(bytes.Slice(at + 4 + first, row.At - first - 1));
                    row.Leb(); row.Leb(true); row.Leb();
                    int pointer = 0, lsda = 255;
                    if (aug.StartsWith('z'))
                    {
                        row.Leb();
                        foreach (char field in aug.AsSpan(1))
                            switch (field)
                            {
                                case 'P': row.Encoded(row.Byte()); break;
                                case 'L': lsda = row.Byte(); break;
                                case 'R': pointer = row.Byte(); break;
                                case 'S': break;
                                default: throw new InvalidDataException("未知 CIE 增补字段");
                            }
                    }
                    else if (aug.Length != 0) throw new InvalidDataException("未知 CIE 增补格式");
                    cies.Add(at, (pointer, lsda, aug.StartsWith('z')));
                }
                else
                {
                    var cie = cies[at + 4 - id];
                    ulong start = row.Encoded(cie.Pointer);
                    ulong size = row.Encoded(cie.Pointer & 15);
                    ulong lsda = 0;
                    if (cie.Augmented && row.Leb() != 0 && cie.Lsda != 255)
                    {
                        lsda = row.Encoded(cie.Lsda);
                        if ((cie.Lsda & 128) != 0 && lsda != 0) lsda = elf.Pointer(lsda);
                    }
                    if (size != 0) ranges.Add(new(start, checked(start + size), lsda));
                }
                at = checked(at + 4 + length);
            }
        }
        frames = ranges.OrderBy(f => f.Start).ToArray();
        tables = frames.Where(f => f.Lsda != 0).Select(f => f.Lsda).Distinct().Order().ToArray();
    }

    public Frame? Find(ulong pc)
    {
        int lo = 0, hi = frames.Length;
        while (lo < hi)
        {
            int mid = lo + (hi - lo) / 2;
            if (frames[mid].Start <= pc) lo = mid + 1; else hi = mid;
        }
        return lo > 0 && pc < frames[lo - 1].End ? frames[lo - 1] : null;
    }

    public CallSite[] Sites(Frame frame) => Sites(frame, out _);

    /// <summary>返回有落地块的调用点。行数包括落地块为零的行。</summary>
    public CallSite[] Sites(Frame frame, out int rowCount)
    {
        rowCount = 0;
        if (frame.Lsda == 0) return [];
        if (exceptions == null || frame.Lsda < exceptions.Address || frame.Lsda - exceptions.Address >= exceptions.Size)
            throw new InvalidDataException("LSDA 地址在异常节外");
        int offset = checked((int)(frame.Lsda - exceptions.Address));
        int index = Array.BinarySearch(tables, frame.Lsda);
        int next = index < 0 ? ~index : index + 1;
        ulong limit = Address(exceptions.Address, exceptions.Size);
        if (next < tables.Length) limit = Math.Min(limit, tables[next]);
        var bytes = file.AsSpan((int)exceptions.Offset + offset, (int)(limit - frame.Lsda));
        var header = new Cursor(bytes, frame.Lsda);
        int encoding = header.Byte();
        ulong landingBase = encoding == 255 ? frame.Start : Pointer(ref header, encoding);
        int typeEncoding = header.Byte();
        int typeEnd = bytes.Length;
        if (typeEncoding != 255)
        {
            ulong distance = header.Leb();
            typeEnd = Offset(header.At, distance, bytes.Length);
        }
        int format = header.Byte();
        if (format is not (0 or 1 or 2 or 3 or 4 or 9 or 10 or 11 or 12)) throw new InvalidDataException("未知 LSDA 调用点编码");
        ulong length = header.Leb();
        int callEnd = Offset(header.At, length, typeEnd);
        var row = new Cursor(bytes[header.At..callEnd], header.Pc);
        var actions = new ActionTable(bytes[callEnd..typeEnd], frame.Lsda + (uint)callEnd, typeEncoding, this);
        var sites = new List<CallSite>();
        while (row.At < (int)length)
        {
            rowCount++;
            ulong start = Address(frame.Start, row.Encoded(format));
            ulong size = row.Encoded(format), landing = row.Encoded(format);
            var (clauses, cleanup, specification) = actions.Read(row.Leb());
            ulong end = Address(start, size);
            if (landing != 0) sites.Add(new(start, end, Address(landingBase, landing), clauses, cleanup, specification));
        }
        return sites.ToArray();
    }

    // 两张表共用这段字节：动作从首字节索引，类型从末尾反向索引。已读区域不能交叠。
    ref struct ActionTable(ReadOnlySpan<byte> data, ulong address, int encoding, UnwindIndex index)
    {
        readonly ReadOnlySpan<byte> bytes = data;
        readonly int width = encoding == 255 ? 0 : TypeWidth(encoding);
        int typeStart = data.Length;
        int actionEnd;

        public (ImmutableArray<UnwindClause>, bool Cleanup, bool Specification) Read(ulong action)
        {
            if (action == 0) return ([], true, false);
            int at = Offset(0, action - 1, typeStart);
            var chain = ImmutableArray.CreateBuilder<UnwindClause>();
            var visited = new HashSet<int>();
            bool cleanup = false, specification = false;
            while (true)
            {
                if (!visited.Add(at)) throw new InvalidDataException("LSDA 动作链有环");
                var record = new Cursor(bytes[..typeStart], address) { At = at };
                long selector = (long)record.Leb(true);
                int displacementAt = record.At;
                long displacement = (long)record.Leb(true);
                actionEnd = Math.Max(actionEnd, record.At);
                if (selector > 0)
                {
                    if (width == 0 || selector > (bytes.Length - actionEnd) / width)
                        throw new InvalidDataException("LSDA 类型表下标越界");
                    int entry = bytes.Length - (int)selector * width;
                    typeStart = Math.Min(typeStart, entry);
                    var type = new Cursor(bytes, address) { At = entry };
                    chain.Add(new(selector, index.Pointer(ref type, encoding)));
                }
                else if (selector == 0) cleanup = true;
                else specification = true;
                if (displacement == 0) return (chain.ToImmutable(), cleanup, specification);
                // ABI 的位移自位移字段的首字节起算，链可以向前回指。
                if (displacement < -displacementAt || displacement >= typeStart - displacementAt)
                    throw new InvalidDataException("LSDA 动作链偏移越界");
                at = displacementAt + (int)displacement;
            }
        }
    }

    ulong Pointer(ref Cursor row, int encoding)
    {
        ulong field = row.Pc;
        ulong value = row.Encoded(encoding);
        // 绝对的 64 位指针字本身也可能带 ELF 重定位。
        if ((encoding & 0x7f) is 0 or 4 or 12) value = elf.Pointer(field);
        return value != 0 && (encoding & 128) != 0 ? elf.Pointer(value) : value;
    }

    static int TypeWidth(int encoding)
    {
        if ((encoding & 0x70) is not (0 or 0x10)) throw new InvalidDataException("未知 DW_EH_PE 基址");
        return (encoding & 15) switch
        {
            0 or 4 or 12 => 8, 2 or 10 => 2, 3 or 11 => 4,
            _ => throw new InvalidDataException("未知 LSDA 类型表项宽度")
        };
    }

    static int Offset(int start, ulong distance, int limit) =>
        start <= limit && distance <= (ulong)(limit - start) ? start + (int)distance : throw new InvalidDataException("LSDA 表偏移越界");

    static ulong Address(ulong start, ulong distance) =>
        distance <= ulong.MaxValue - start ? start + distance : throw new InvalidDataException("LSDA 地址越界");
}
