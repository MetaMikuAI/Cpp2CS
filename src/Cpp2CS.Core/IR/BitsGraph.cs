using System.Runtime.CompilerServices;

namespace Cpp2CS.IR;

// 位值不可变；共享子图只计算一次，哈希碰撞仍逐项比较完整结构。
internal static class BitsGraph
{
    private sealed record HashEntry(int Value);
    private static readonly ConditionalWeakTable<Bits, HashEntry> hashes = new();
    private static IReadOnlyList<Bits> Children(Bits value) => value switch
    {
        SliceBits slice => [slice.Source],
        ConcatBits concat => concat.Parts,
        PhiBits phi => phi.Incoming,
        _ => []
    };
    public static int Hash(Bits value)
    {
        if (hashes.TryGetValue(value, out var known)) return known.Value;
        var pending = new Stack<(Bits Value, bool Expanded)>();
        pending.Push((value, false));
        while (pending.TryPop(out var item))
        {
            if (hashes.TryGetValue(item.Value, out _)) continue;
            var children = Children(item.Value);
            if (!item.Expanded && children.Count > 0)
            {
                pending.Push((item.Value, true));
                foreach (var child in children) pending.Push((child, false));
                continue;
            }
            var hash = new HashCode();
            hash.Add(item.Value.GetType());
            hash.Add(item.Value.Width);
            switch (item.Value)
            {
                case SliceBits slice: hash.Add(slice.Offset); hash.Add(slice.BitWidth); break;
                case ConcatBits concat: hash.Add(concat.BitWidth); break;
                case PhiBits phi: hash.Add(phi.Block); hash.Add(phi.BitWidth); break;
                default: hash.Add(item.Value.GetHashCode()); break;
            }
            foreach (var child in children) hash.Add(hashes.GetValue(child, _ => throw new InvalidOperationException("位值子节点未计算")).Value);
            var entry = new HashEntry(hash.ToHashCode());
            hashes.GetValue(item.Value, _ => entry);
        }
        return hashes.GetValue(value, _ => throw new InvalidOperationException("位值哈希未计算")).Value;
    }
    public static bool Equal(Bits left, Bits? right)
    {
        if (ReferenceEquals(left, right)) return true;
        if (right is null || Hash(left) != Hash(right)) return false;
        var pending = new Stack<(Bits Left, Bits Right)>();
        var seen = new HashSet<(Bits, Bits)>(PairIdentity.Instance);
        pending.Push((left, right));
        while (pending.TryPop(out var pair))
        {
            var a = pair.Left; var b = pair.Right;
            if (ReferenceEquals(a, b) || !seen.Add(pair)) continue;
            if (a.GetType() != b.GetType() || a.Width != b.Width) return false;
            var same = (a, b) switch
            {
                (SliceBits x, SliceBits y) => x.Offset == y.Offset && x.BitWidth == y.BitWidth,
                (ConcatBits x, ConcatBits y) => x.BitWidth == y.BitWidth,
                (PhiBits x, PhiBits y) => x.Block == y.Block && x.BitWidth == y.BitWidth,
                _ => a.Equals(b)
            };
            if (!same) return false;
            var first = Children(a); var second = Children(b);
            if (first.Count != second.Count) return false;
            for (var index = 0; index < first.Count; index++) pending.Push((first[index], second[index]));
        }
        return true;
    }
    private sealed class PairIdentity : IEqualityComparer<(Bits Left, Bits Right)>
    {
        public static readonly PairIdentity Instance = new();
        public bool Equals((Bits Left, Bits Right) x, (Bits Left, Bits Right) y) => ReferenceEquals(x.Left, y.Left) && ReferenceEquals(x.Right, y.Right);
        public int GetHashCode((Bits Left, Bits Right) pair) => HashCode.Combine(RuntimeHelpers.GetHashCode(pair.Left), RuntimeHelpers.GetHashCode(pair.Right));
    }
}
