using System.Numerics;
using Cpp2CS.Model;

namespace Cpp2CS.IR;

public abstract record Bits(int Width);
public sealed record InputBits(string Identity, int BitWidth) : Bits(BitWidth);
public sealed record ConstantBits(BigInteger Value, int BitWidth) : Bits(BitWidth);
public sealed record SliceBits(Bits Source, int Offset, int BitWidth) : Bits(BitWidth);
// Parts 按低位到高位排列。
public sealed record ConcatBits(Sequence<Bits> Parts, int BitWidth) : Bits(BitWidth);
public sealed record UnknownBits(string Identity, string Reason, int BitWidth) : Bits(BitWidth);
public sealed record PhiBits(string Block, Sequence<Bits> Incoming, int BitWidth) : Bits(BitWidth);

public static class BitOps
{
    public static Bits Constant(BigInteger value, int width)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(width);
        return new ConstantBits(value & ((BigInteger.One << width) - 1), width);
    }
    public static Bits Slice(Bits source, int offset, int width)
    {
        if (offset < 0 || width <= 0 || (long)offset + width > source.Width) throw new ArgumentOutOfRangeException(nameof(offset));
        if (offset == 0 && width == source.Width) return source;
        if (source is ConstantBits c) return Constant(c.Value >> offset, width);
        if (source is SliceBits s) return Slice(s.Source, checked(s.Offset + offset), width);
        if (source is ConcatBits joined)
        {
            var parts = new List<Bits>();
            var position = 0;
            foreach (var part in joined.Parts)
            {
                var start = Math.Max(position, offset);
                var end = Math.Min(position + part.Width, offset + width);
                if (start < end) parts.Add(Slice(part, start - position, end - start));
                position += part.Width;
            }
            return Concat(parts);
        }
        return new SliceBits(source, offset, width);
    }
    public static Bits Concat(IEnumerable<Bits> source)
    {
        var parts = source.ToArray();
        if (parts.Length == 0 || parts.Any(x => x.Width <= 0)) throw new ArgumentException("拼接需要有效位宽");
        if (parts.Length == 1) return parts[0];
        var width = checked(parts.Sum(x => x.Width));
        if (parts.All(x => x is ConstantBits))
        {
            BigInteger value = 0;
            var shift = 0;
            foreach (var part in parts.Cast<ConstantBits>()) { value |= part.Value << shift; shift += part.Width; }
            return Constant(value, width);
        }
        if (parts[0] is SliceBits first)
        {
            var offset = first.Offset;
            var continuous = true;
            foreach (var part in parts)
            {
                if (part is not SliceBits s || s.Source != first.Source || s.Offset != offset) { continuous = false; break; }
                offset += part.Width;
            }
            if (continuous) return Slice(first.Source, first.Offset, width);
        }
        return new ConcatBits(new(parts), width);
    }
    public static Bits Phi(string block, IEnumerable<Bits> incoming)
    {
        var values = incoming.ToArray();
        if (values.Length == 0 || values.Any(x => x.Width != values[0].Width)) throw new ArgumentException("合流位宽不一致");
        return values.All(x => x == values[0]) ? values[0] : new PhiBits(block, new(values), values[0].Width);
    }
}
