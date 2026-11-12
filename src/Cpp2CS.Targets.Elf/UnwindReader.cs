using System.Collections.Immutable;
using Cpp2CS.Native.Images;

namespace Cpp2CS.Targets.Elf;

/// <summary>只解释展开记录的范围和语言异常数据，不解释指令与展开操作码。</summary>
internal sealed class UnwindReader
{
    private readonly LoadedImage image;
    private readonly Dictionary<PointerTarget, string?> typeNames = [];
    internal List<FunctionRange> Functions { get; } = [];
    internal List<TryRegion> Regions { get; } = [];
    internal List<string> Diagnostics { get; } = [];

    internal UnwindReader(LoadedImage image, ImageDocument document)
    {
        this.image = image;
        if (document.EhFrameHeader is not { } va)
        {
            Diagnostics.Add("没有展开索引；函数范围仅来自有长度的符号");
            return;
        }
        var start = image.Offset(va);
        var c = new Cursor(image, start);
        if (c.Byte() != 1) throw new NotSupportedException("展开索引版本未支持");
        var pointerEncoding = c.Byte();
        var countEncoding = c.Byte();
        var tableEncoding = c.Byte();
        _ = Encoded(c, pointerEncoding, start);
        var count = Scalar(c, countEncoding);
        if (count > (ulong)document.Bytes.Length / 8) throw new InvalidDataException("展开索引数量越界");
        ulong previous = 0;
        for (ulong i = 0; i < count; i++)
        {
            var function = Encoded(c, tableEncoding, start);
            var fde = Encoded(c, tableEncoding, start);
            if (i != 0 && function < previous) throw new InvalidDataException("展开索引未排序");
            previous = function;
            ReadFde(fde, function);
        }
    }

    private void ReadFde(ulong at, ulong indexedStart)
    {
        var f = Record(at);
        var ciePointerAt = f.Position;
        var distance = f.Unsigned(4);
        if (distance > ciePointerAt) throw new InvalidDataException("展开公共记录指针越界");
        var c = Record(ciePointerAt - distance);
        if (c.Unsigned(4) != 0) throw new InvalidDataException("展开公共记录标识错误");
        var version = c.Byte();
        if (version is not (1 or 3)) throw new NotSupportedException($"展开公共记录版本 {version} 未支持");
        var augmentation = c.String();
        _ = c.Uleb();
        _ = c.Sleb();
        if (version == 1) _ = c.Byte(); else _ = c.Uleb();
        byte functionEncoding = 0, languageEncoding = 0xff;
        var augmented = augmentation.StartsWith('z');
        if (augmentation.Length != 0 && !augmented) throw new NotSupportedException("展开增强缺少长度");
        if (augmented)
        {
            var size = c.Uleb();
            var end = Add(c.Position, size);
            if (end > c.End) throw new InvalidDataException("展开增强长度越界");
            foreach (var letter in augmentation[1..])
                switch (letter)
                {
                    case 'R': functionEncoding = c.Byte(); break;
                    case 'L': languageEncoding = c.Byte(); break;
                    case 'P': var encoding = c.Byte(); _ = Encoded(c, (byte)(encoding & 0x7f), 0); break;
                    case 'S': break;
                    default: throw new NotSupportedException($"展开增强 {letter} 未支持");
                }
            if (c.Position != end) throw new InvalidDataException("展开增强长度不匹配");
        }
        var start = Encoded(f, functionEncoding, 0);
        var length = Scalar(f, (byte)(functionEncoding & 15));
        if (length == 0 && start == indexedStart)
        {
            Diagnostics.Add($"展开记录 0x{at:x} 长度为零，不能提供函数范围");
            return;
        }
        if (start != indexedStart || !image.IsExecutable(start, length)) throw new InvalidDataException($"展开范围与索引或可执行映射不一致：record=0x{at:x}, start=0x{start:x}, index=0x{indexedStart:x}, length=0x{length:x}");
        Functions.Add(new(start, length, FunctionEvidence.UnwindTable));
        if (augmented)
        {
            var size = f.Uleb();
            var end = Add(f.Position, size);
            if (end > f.End) throw new InvalidDataException("展开函数增强越界");
            if (languageEncoding != 0xff)
            {
                var language = Encoded(f, languageEncoding, 0);
                ReadLanguage(language, start, Add(start, length));
            }
            if (f.Position != end) throw new InvalidDataException("展开函数增强长度不匹配");
        }
    }

    private Cursor Record(ulong at)
    {
        var c = new Cursor(image, at);
        var length = c.Unsigned(4);
        if (length is 0 or 0xffffffff) throw new NotSupportedException("展开记录长度未支持");
        c.End = Add(c.Position, length);
        return c;
    }

    private void ReadLanguage(ulong at, ulong start, ulong end)
    {
        var c = new Cursor(image, at);
        var baseEncoding = c.Byte();
        var landingBase = baseEncoding == 0xff ? start : Encoded(c, baseEncoding, 0);
        var typeEncoding = c.Byte();
        ulong? typeEnd = null;
        if (typeEncoding != 0xff) { var delta = c.Uleb(); typeEnd = Add(c.Position, delta); }
        var callEncoding = c.Byte();
        var tableSize = c.Uleb();
        var tableEnd = Add(c.Position, tableSize);
        c.End = tableEnd;
        var records = new List<(ulong Start, ulong Length, ulong? Handler, ulong Action)>();
        ulong previous = start;
        while (c.Position < tableEnd)
        {
            var first = Add(landingBase, Scalar(c, callEncoding));
            var length = Scalar(c, callEncoding);
            var landing = Scalar(c, callEncoding);
            var action = c.Uleb();
            ulong? handler = landing == 0 ? null : Add(landingBase, landing);
            if (first < start || first < previous || Add(first, length) > end ||
                (handler is { } h && !image.IsExecutable(h)) || (handler == null && action != 0))
                throw new InvalidDataException("异常调用区间或处理入口越界");
            previous = Add(first, length);
            records.Add((first, length, handler, action));
        }
        PointerTarget ReadType(ulong index)
        {
            if (typeEnd is not { } limit) throw new InvalidDataException("异常匹配缺少类型表");
            var width = Width(typeEncoding);
            if (index > limit / (ulong)width) throw new InvalidDataException("异常类型索引越界");
            var entry = limit - index * (ulong)width;
            if (entry < tableEnd) throw new InvalidDataException("异常类型表越界");
            return TypeTarget(new Cursor(image, entry, limit), typeEncoding);
        }
        foreach (var r in records)
        {
            var clauses = new List<ExceptionClause>();
            if (r.Action == 0 && r.Handler != null) clauses.Add(new(ClauseKind.Cleanup, []));
            if (r.Action != 0)
            {
                var action = new Cursor(image, Add(tableEnd, r.Action - 1), typeEnd ?? ulong.MaxValue);
                var visited = new HashSet<ulong>();
                while (true)
                {
                    if (action.Position < tableEnd || !visited.Add(action.Position)) throw new InvalidDataException("异常动作链越界或成环");
                    var filter = action.Sleb();
                    var nextAt = action.Position;
                    var next = action.Sleb();
                    if (filter == 0) clauses.Add(new(ClauseKind.Cleanup, []));
                    else if (filter < 0)
                    {
                        if (typeEnd is not { } limit) throw new InvalidDataException("异常规格缺少类型表");
                        // libc++abi exception_spec_can_catch：负索引是类型表末尾之后的一基字节偏移。
                        var list = new Cursor(image, Add(limit, unchecked(0UL - (ulong)filter) - 1));
                        var matches = ImmutableArray.CreateBuilder<PointerTarget>();
                        ulong index;
                        while ((index = list.Uleb()) != 0) matches.Add(ReadType(index));
                        clauses.Add(new(ClauseKind.ExceptionSpecification, matches.ToImmutable()) { Selector = filter });
                    }
                    else
                    {
                        var type = ReadType((ulong)filter);
                        clauses.Add(new(type is PointerTarget.Null ? ClauseKind.CatchAll : ClauseKind.Catch, type is PointerTarget.Null ? [] : [type])
                        { Selector = filter, TypeName = TypeName(type) });
                    }
                    if (next == 0) break;
                    action.Position = SignedAdd(nextAt, next);
                }
            }
            Regions.Add(new(r.Start, r.Length, r.Handler, clauses.ToImmutableArray()));
        }
    }

    // Itanium type_info 的第二个指针是名字串；映像层只保留名字，不解释运行时身份。
    private string? TypeName(PointerTarget type)
    {
        if (!typeNames.TryGetValue(type, out var name)) typeNames.Add(type, name = ReadTypeName(type));
        return name;
    }
    private string? ReadTypeName(PointerTarget type)
    {
        if (type is not PointerTarget.Internal info || image.Query(info.Offset).AvailableBytes < (ulong)(2 * image.PointerWidth)
            || image.ReadPointer(info.Offset + (ulong)image.PointerWidth) is not PointerTarget.Internal name) return null;
        var text = new System.Text.StringBuilder();
        var available = image.Query(name.Offset).AvailableBytes;
        for (ulong i = 0; i < available; i++)
        {
            var value = image.ReadUnsigned(name.Offset + i, 1);
            if (value == 0) return text.ToString();
            if (value > 127) return null;
            text.Append((char)value);
        }
        return null;
    }

    private PointerTarget TypeTarget(Cursor c, byte encoding)
    {
        var at = c.Position;
        if ((encoding & 0x7f) == 0) return image.ReadPointer(at);
        var raw = Scalar(c, (byte)(encoding & 15));
        if (raw == 0) return new PointerTarget.Null();
        var target = Relative(raw, encoding, at, 0);
        return (encoding & 0x80) != 0 ? image.ReadPointer(target) : new PointerTarget.Internal(target);
    }

    private ulong Encoded(Cursor c, byte encoding, ulong dataBase)
    {
        if (encoding == 0xff) throw new NotSupportedException("缺少指针编码");
        var at = c.Position;
        var raw = Scalar(c, (byte)(encoding & 15));
        var target = Relative(raw, encoding, at, dataBase);
        if ((encoding & 0x80) == 0) return target;
        return image.ReadPointer(target) is PointerTarget.Internal value ? value.Offset : throw new InvalidDataException("展开指针不能解析为内部地址");
    }
    private ulong Relative(ulong raw, byte encoding, ulong at, ulong dataBase) => (encoding & 0x70) switch
    {
        0 => image.Offset(raw),
        0x10 => SignedAdd(at, unchecked((long)raw)),
        0x30 => SignedAdd(dataBase, unchecked((long)raw)),
        _ => throw new NotSupportedException("指针相对基准未支持")
    };
    private static int Width(byte encoding) => (encoding & 15) switch
    {
        0 or 4 or 12 => 8, 2 or 10 => 2, 3 or 11 => 4,
        _ => throw new NotSupportedException("变长类型表条目未支持")
    };
    private static ulong Scalar(Cursor c, byte encoding) => encoding switch
    {
        0 or 4 => c.Unsigned(8), 1 => c.Uleb(), 2 => c.Unsigned(2), 3 => c.Unsigned(4),
        9 => unchecked((ulong)c.Sleb()), 10 => unchecked((ulong)(short)c.Unsigned(2)),
        11 => unchecked((ulong)(int)c.Unsigned(4)), 12 => c.Unsigned(8),
        _ => throw new NotSupportedException($"数值编码 {encoding:x} 未支持")
    };
    private static ulong Add(ulong a, ulong b) => b <= ulong.MaxValue - a ? a + b : throw new InvalidDataException("地址溢出");
    private static ulong SignedAdd(ulong a, long b) => b >= 0 ? Add(a, (ulong)b) :
        unchecked(0UL - (ulong)b) <= a ? a - unchecked(0UL - (ulong)b) : throw new InvalidDataException("相对地址下溢");

    private sealed class Cursor(LoadedImage image, ulong position, ulong end = ulong.MaxValue)
    {
        internal ulong Position { get; set; } = position;
        internal ulong End { get; set; } = end;
        internal ulong Unsigned(int width)
        {
            if (Position > End || (ulong)width > End - Position) throw new InvalidDataException("记录截断");
            var value = image.ReadUnsigned(Position, width);
            Position = Add(Position, (ulong)width);
            return value;
        }
        internal byte Byte() => (byte)Unsigned(1);
        internal string String()
        {
            var result = new System.Text.StringBuilder();
            byte b;
            while ((b = Byte()) != 0) result.Append((char)b);
            return result.ToString();
        }
        internal ulong Uleb()
        {
            ulong value = 0;
            for (var shift = 0; shift < 64; shift += 7)
            {
                var b = Byte();
                if (shift == 63 && b > 1) throw new InvalidDataException("变长整数溢出");
                value |= (ulong)(b & 127) << shift;
                if ((b & 128) == 0) return value;
            }
            throw new InvalidDataException("变长整数未终止");
        }
        internal long Sleb()
        {
            ulong value = 0;
            for (var shift = 0; shift < 64; shift += 7)
            {
                var b = Byte();
                if (shift == 63 && b is not (0 or 127)) throw new InvalidDataException("有符号变长整数溢出");
                value |= (ulong)(b & 127) << shift;
                if ((b & 128) != 0) continue;
                if (shift < 57 && (b & 64) != 0) value |= ulong.MaxValue << (shift + 7);
                return unchecked((long)value);
            }
            throw new InvalidDataException("有符号变长整数未终止");
        }
    }
}
