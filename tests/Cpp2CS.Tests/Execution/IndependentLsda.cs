using System.Buffers.Binary;
using Cpp2CS.Images;

namespace Cpp2CS.Tests.Execution;

internal sealed record UnwindAction(ulong Address, long Filter, long Next, ulong? TypeSlot, ulong? TypeInfo)
{
    public string Kind => Filter == 0 ? "cleanup" : Filter < 0 ? "exception-specification-unresolved" : TypeInfo == 0 ? "catch-all" : "typed-catch";
}
internal sealed record UnwindSite(ulong Start, ulong End, ulong Landing, ulong ActionOffset, UnwindAction[] Actions);
internal sealed record UnwindTable(ulong Start, ulong End, ulong Lsda, byte TypeEncoding, UnwindSite[] Sites);

/// <summary>
/// 测试侧独立读取 .eh_frame 和 LSDA；不引用 Core 的 FunctionTable/ExceptionTable。
/// 格式依据 LLVM libcxxabi cxa_personality.cpp 的 scan_eh_tab/readEncodedPointer；
/// .eh_frame 的 CIE/FDE 依据 LSB Exception Frames。映像映射和加载器重定位仍由 ImageDocument 提供。
/// </summary>
internal static class IndependentLsda
{
    internal sealed class Reader(Func<ulong, int, byte[]> read, Func<ulong, ulong?> pointer)
    {
        public ulong Position;
        public byte Byte() => read(Position++, 1)[0];
        public ulong Unsigned()
        {
            ulong result = 0; var shift = 0;
            while (true)
            {
                var b = Byte();
                if (shift == 63 && (b & 0xfe) != 0 || shift > 63) throw new InvalidDataException("ULEB128 overflow");
                result |= (ulong)(b & 0x7f) << shift;
                if (b < 128) return result;
                shift += 7;
            }
        }
        public long Signed()
        {
            long result = 0; var bits = 0; byte b;
            do
            {
                b = Byte();
                if (bits == 63 && b is not (0 or 127) || bits > 63) throw new InvalidDataException("SLEB128 overflow");
                result |= (long)(b & 127) << bits; bits += 7;
            } while ((b & 128) != 0);
            return bits < 64 && (b & 64) != 0 ? result | (-1L << bits) : result;
        }
        public ulong Fixed(int size)
        {
            var bytes = read(Position, size); Position += (ulong)size;
            return size switch { 2 => BinaryPrimitives.ReadUInt16LittleEndian(bytes), 4 => BinaryPrimitives.ReadUInt32LittleEndian(bytes), 8 => BinaryPrimitives.ReadUInt64LittleEndian(bytes), _ => throw new NotSupportedException() };
        }
        public ulong Encoded(byte encoding, bool relocate = true)
        {
            if (encoding == 0xff) return 0;
            var at = Position;
            ulong value = (encoding & 15) switch
            {
                0 or 4 => Fixed(8), 1 => Unsigned(), 2 => Fixed(2), 3 => Fixed(4),
                9 => unchecked((ulong)Signed()), 10 => unchecked((ulong)(short)Fixed(2)),
                11 => unchecked((ulong)(int)Fixed(4)), 12 => Fixed(8),
                _ => throw new NotSupportedException($"DW_EH_PE 0x{encoding:x}")
            };
            if ((encoding & 0x70) is not (0 or 0x10)) throw new NotSupportedException("DW_EH_PE relative base");
            if (value != 0 && (encoding & 0x70) == 0x10) value = unchecked(at + value);
            else if (relocate && encoding == 0) value = pointer(at) ?? throw new InvalidDataException("unresolved absolute pointer");
            if (value != 0 && (encoding & 0x80) != 0) value = pointer(value) ?? throw new InvalidDataException("unresolved indirect pointer");
            return value;
        }
    }

    private sealed record Cie(byte CodeEncoding, byte LsdaEncoding, bool Augmented);
    public static UnwindTable[] ReadImage(ImageDocument image)
    {
        var section = image.Section(".eh_frame") ?? throw new InvalidDataException("缺少 .eh_frame");
        var r = new Reader((a, n) => image.Read(a, n).ToArray(), image.ReadPointer);
        var cies = new Dictionary<ulong, Cie>();
        var tables = new List<UnwindTable>();
        for (var record = section.Address; record < section.Address + section.Size;)
        {
            r.Position = record;
            var size = r.Fixed(4);
            if (size == 0) break;
            if (size == uint.MaxValue) throw new NotSupportedException("DWARF64 .eh_frame");
            var end = checked(record + 4 + size);
            if (end > section.Address + section.Size) throw new InvalidDataException("FDE/CIE 越界");
            var idAt = r.Position; var id = r.Fixed(4);
            if (id == 0)
            {
                if (r.Byte() != 1) throw new NotSupportedException("CIE version");
                var aug = ""; byte ch;
                while ((ch = r.Byte()) != 0 && r.Position < end) aug += (char)ch;
                _ = r.Unsigned(); _ = r.Signed(); _ = r.Unsigned();
                byte code = 0, lsda = 0xff;
                if (!aug.StartsWith('z')) throw new NotSupportedException("CIE augmentation");
                var bytes = r.Unsigned(); var augEnd = checked(r.Position + bytes);
                foreach (var flag in aug.Skip(1))
                    switch (flag)
                    {
                        case 'R': code = r.Byte(); break;
                        case 'L': lsda = r.Byte(); break;
                        case 'P': _ = r.Encoded(r.Byte()); break;
                        default: throw new NotSupportedException($"CIE flag {flag}");
                    }
                if (r.Position != augEnd || augEnd > end) throw new InvalidDataException("CIE augmentation length");
                cies.Add(record, new(code, lsda, true));
            }
            else
            {
                var cie = cies[checked(idAt - id)];
                var start = r.Encoded(cie.CodeEncoding);
                var length = r.Encoded((byte)(cie.CodeEncoding & 15), false);
                var bytes = r.Unsigned(); var augEnd = checked(r.Position + bytes);
                var lsda = cie.LsdaEncoding == 0xff ? 0 : r.Encoded(cie.LsdaEncoding);
                if (r.Position != augEnd || augEnd > end) throw new InvalidDataException("FDE augmentation length");
                if (lsda != 0 && length != 0) tables.Add(Read(r, lsda, start, checked(start + length)));
            }
            record = end;
        }
        return tables.ToArray();
    }

    public static UnwindTable Read(Reader r, ulong lsda, ulong start, ulong end)
    {
        r.Position = lsda;
        var landingEncoding = r.Byte();
        var landingBase = landingEncoding == 0xff ? start : r.Encoded(landingEncoding);
        var typeEncoding = r.Byte();
        ulong typeBase = 0;
        if (typeEncoding != 0xff)
        {
            var distance = r.Unsigned();
            typeBase = checked(r.Position + distance);
        }
        var siteEncoding = r.Byte();
        var siteBytes = r.Unsigned(); var actionBase = checked(r.Position + siteBytes);
        var raw = new List<(ulong Start, ulong End, ulong Pad, ulong Action)>();
        while (r.Position < actionBase)
        {
            var offset = r.Encoded(siteEncoding, false); var count = r.Encoded(siteEncoding, false);
            var pad = r.Encoded(siteEncoding, false); var action = r.Unsigned();
            raw.Add((checked(landingBase + offset), checked(landingBase + offset + count), pad == 0 ? 0 : checked(landingBase + pad), action));
        }
        if (r.Position != actionBase) throw new InvalidDataException("call-site length");
        var result = new List<UnwindSite>();
        foreach (var site in raw)
        {
            if (site.Start < start || site.End > end || site.End < site.Start || site.Pad != 0 && (site.Pad < start || site.Pad >= end) ||
                result.Count > 0 && result[^1].End > site.Start || site.Pad == 0 && site.Action != 0) throw new InvalidDataException("call-site range");
            var actions = new List<UnwindAction>();
            var visited = new HashSet<ulong>();
            var address = site.Action == 0 ? 0 : checked(actionBase + site.Action - 1);
            while (address != 0)
            {
                if (address < actionBase || address - actionBase > 65536 || typeBase != 0 && address >= typeBase || !visited.Add(address))
                    throw new InvalidDataException("action chain range/cycle");
                r.Position = address; var filter = r.Signed(); var displacementAt = r.Position; var next = r.Signed();
                ulong? slot = null, type = null;
                if (filter > 0)
                {
                    var width = (typeEncoding & 15) switch { 0 or 4 or 12 => 8, 2 or 10 => 2, 3 or 11 => 4, _ => throw new NotSupportedException("variable-length type table") };
                    var entry = checked(typeBase - checked((ulong)filter * (ulong)width));
                    if (entry < actionBase) throw new InvalidDataException("type table index");
                    r.Position = entry;
                    // TypeSlot 用于逐项比较 Core 的槽位；TypeInfo 是独立解码后实际运行时类型。
                    slot = typeEncoding == 0 ? entry : r.Encoded((byte)(typeEncoding & 0x7f));
                    r.Position = entry; type = r.Encoded(typeEncoding);
                    if (type == 0 && typeEncoding != 0) slot = 0;
                }
                actions.Add(new(address, filter, next, slot, type));
                address = next == 0 ? 0 : checked((ulong)((long)displacementAt + next));
            }
            result.Add(new(site.Start, site.End, site.Pad, site.Action, actions.ToArray()));
        }
        return new(start, end, lsda, typeEncoding, result.ToArray());
    }
}
