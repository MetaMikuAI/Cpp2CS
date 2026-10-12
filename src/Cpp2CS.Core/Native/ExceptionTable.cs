using System.Buffers.Binary;

namespace Cpp2CS.Native;

public sealed record ExceptionAction(ulong Address, long Filter, long NextOffset, ulong? TypeInfo, string Kind);
public sealed record ExceptionRegion(ulong Start, ulong End, ulong? LandingPad, ulong ActionOffset)
{
    public ExceptionAction[] Actions { get; init; } = [];
}

public static class ExceptionTable
{
    public static ExceptionRegion[] Read(ElfImage image, ulong address, ulong functionStart, ulong functionEnd) =>
        Read(image.Read, image.ReadResolvedPointer, address, functionStart, functionEnd);

    // next 偏移以 next 字段自身为基准；类型表从表尾向低地址索引。
    public static ExceptionRegion[] Read(Func<ulong, int, byte[]> read, Func<ulong, ulong> pointer,
        ulong address, ulong functionStart, ulong functionEnd)
    {
        var cursor = address;
        byte Byte() => read(cursor++, 1)[0];
        ulong Uleb()
        {
            ulong value = 0;
            for (var shift = 0; shift < 64; shift += 7)
            {
                var b = Byte();
                if (shift == 63 && b > 1) throw new InvalidDataException("LSDA ULEB128 溢出");
                value |= (ulong)(b & 127) << shift;
                if ((b & 128) == 0) return value;
            }
            throw new InvalidDataException("LSDA ULEB128 过长");
        }
        long Sleb()
        {
            ulong value = 0;
            for (var shift = 0; shift < 64; shift += 7)
            {
                var b = Byte();
                if (shift == 63 && b is not (0 or 127)) throw new InvalidDataException("LSDA SLEB128 溢出");
                value |= (ulong)(b & 127) << shift;
                if ((b & 128) != 0) continue;
                if (shift < 57 && (b & 64) != 0) value |= ulong.MaxValue << (shift + 7);
                return unchecked((long)value);
            }
            throw new InvalidDataException("LSDA SLEB128 过长");
        }
        if (Byte() != 0xff) throw new InvalidDataException("尚未支持显式 LPStart");
        var typeEncoding = Byte();
        ulong? typeEnd = null;
        if (typeEncoding != 0xff) { var delta = Uleb(); typeEnd = checked(cursor + delta); }
        if (Byte() != 1) throw new InvalidDataException("尚未支持非 ULEB128 call-site table");
        var length = Uleb();
        if (length > 65536) throw new InvalidDataException("LSDA call-site table 超出限制");
        var end = checked(cursor + length);
        var regions = new List<ExceptionRegion>();
        while (cursor < end)
        {
            var start = checked(functionStart + Uleb());
            var limit = checked(start + Uleb());
            var landing = Uleb(); var action = Uleb();
            if (start < functionStart || limit > functionEnd || limit < start || landing != 0 && checked(functionStart + landing) >= functionEnd ||
                regions.Count > 0 && start < regions[^1].End || landing == 0 && action != 0)
                throw new InvalidDataException("LSDA 区间重叠或超出函数范围");
            regions.Add(new(start, limit, landing == 0 ? null : checked(functionStart + landing), action));
        }
        if (cursor != end) throw new InvalidDataException("LSDA call-site table 长度不匹配");
        return regions.Select(region => region with { Actions = Actions(region.ActionOffset) }).ToArray();

        ExceptionAction[] Actions(ulong offset)
        {
            if (offset == 0) return [];
            var actions = new List<ExceptionAction>();
            cursor = checked(end + offset - 1);
            var visited = new HashSet<ulong>();
            while (true)
            {
                if (cursor < end || cursor - end > 65536 || typeEnd is { } limit && cursor >= limit || !visited.Add(cursor))
                    throw new InvalidDataException("LSDA action 链越界或成环");
                var at = cursor;
                var filter = Sleb();
                var nextAt = cursor;
                var next = Sleb();
                var type = filter > 0 ? TypeInfo(filter) : null;
                actions.Add(new(at, filter, next, type, filter == 0 ? "cleanup" :
                    filter < 0 ? "exception-specification-unresolved" : type == 0 ? "catch-all" : "typed-catch"));
                if (next == 0) return actions.ToArray();
                cursor = checked((ulong)((long)nextAt + next));
            }
        }
        ulong? TypeInfo(long index)
        {
            if (typeEnd is null) throw new InvalidDataException("LSDA catch 缺少类型表");
            var width = (typeEncoding & 15) switch { 0 or 4 or 12 => 8, 3 or 11 => 4, _ => 0 };
            if (width == 0 || (typeEncoding & 0x70) is not (0 or 0x10))
                throw new InvalidDataException($"不支持 LSDA 类型指针编码 0x{typeEncoding:x}");
            var at = checked(typeEnd.Value - checked((ulong)index * (ulong)width));
            if (at < end) throw new InvalidDataException("LSDA 类型索引越界");
            var bytes = read(at, width);
            if (typeEncoding == 0) return pointer(at);
            long raw = width == 8 ? BinaryPrimitives.ReadInt64LittleEndian(bytes) :
                (typeEncoding & 15) == 11 ? BinaryPrimitives.ReadInt32LittleEndian(bytes) : BinaryPrimitives.ReadUInt32LittleEndian(bytes);
            if (raw == 0) return 0;
            var value = (typeEncoding & 0x70) == 0x10 ? checked((ulong)((long)at + raw)) : unchecked((ulong)raw);
            return (typeEncoding & 0x80) != 0 ? pointer(value) : value;
        }
    }
}
