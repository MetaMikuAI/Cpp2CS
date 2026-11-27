using System.Buffers.Binary;
using Cpp2CS.Input;

namespace Cpp2CS.Target;

public readonly record struct Frame(ulong Start, ulong End, ulong Lsda);
public readonly record struct CallSite(ulong Start, ulong End, ulong Landing);

/// <summary>LSB .eh_frame 的 CIE/FDE 及 Itanium 异常 ABI 的调用点表。地址为链接虚拟地址。</summary>
public sealed class UnwindIndex
{
    readonly Frame[] frames;
    public ReadOnlySpan<Frame> Frames => frames;
    readonly byte[] file;
    readonly Elf64 elf;
    readonly ElfSection? exceptions;

    ref struct Cursor(ReadOnlySpan<byte> source, ulong address)
    {
        readonly ReadOnlySpan<byte> data = source;
        public int At;
        public ulong Pc => checked(address + (uint)At);
        public byte Byte() => data[At++];
        public uint Word()
        {
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

    public CallSite[] Sites(Frame frame)
    {
        if (frame.Lsda == 0) return [];
        if (exceptions == null || frame.Lsda < exceptions.Address || frame.Lsda - exceptions.Address >= exceptions.Size)
            throw new InvalidDataException("LSDA 地址在异常节外");
        int offset = checked((int)(frame.Lsda - exceptions.Address));
        var row = new Cursor(file.AsSpan((int)exceptions.Offset + offset, (int)exceptions.Size - offset), frame.Lsda);
        int encoding = row.Byte();
        ulong landingBase = encoding == 255 ? frame.Start : row.Encoded(encoding);
        if ((encoding & 128) != 0 && encoding != 255) landingBase = elf.Pointer(landingBase);
        if (row.Byte() != 255) row.Leb();
        int format = row.Byte();
        int length = checked((int)row.Leb());
        int end = checked(row.At + length);
        var sites = new List<CallSite>();
        while (row.At < end)
        {
            ulong start = checked(frame.Start + row.Encoded(format));
            ulong size = row.Encoded(format), landing = row.Encoded(format);
            row.Leb();
            if (landing != 0) sites.Add(new(start, checked(start + size), checked(landingBase + landing)));
        }
        if (row.At != end) throw new InvalidDataException("LSDA 调用点表长度不符");
        return sites.ToArray();
    }
}
