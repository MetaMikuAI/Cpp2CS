
namespace Cpp2CS.Machine.Storage;



/// <summary>整值复制必须精确覆盖每个叶子一次；重复叶子不算完整。</summary>
internal static class ValueCoverage
{
    public sealed class PathComparer<T> : IEqualityComparer<IReadOnlyList<T>>
    {
        public bool Equals(IReadOnlyList<T>? left, IReadOnlyList<T>? right) => left is not null && right is not null && left.SequenceEqual(right);
        public int GetHashCode(IReadOnlyList<T> path) => path.Aggregate(17, (hash, item) => HashCode.Combine(hash, item));
    }
    public static bool Exact<T>(IReadOnlyCollection<T> expected, IEnumerable<T> actual, IEqualityComparer<T> comparer)
    {
        var remaining = new HashSet<T>(expected, comparer);
        if (remaining.Count != expected.Count) return false;
        foreach (var item in actual)
            if (!remaining.Remove(item)) return false;
        return remaining.Count == 0;
    }

    public static IEnumerable<StorageRange> Merge(IEnumerable<StorageRange> ranges)
    {
        StorageRange? current = null;
        foreach (var range in ranges.OrderBy(r => r.Offset))
        {
            if (current is not { } previous) { current = range; continue; }
            if (range.Offset > previous.End) { yield return previous; current = range; }
            else current = new(previous.Offset, checked((int)(Math.Max(previous.End, range.End) - previous.Offset)));
        }
        if (current is { } last) yield return last;
    }
}
