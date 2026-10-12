using System.Collections;
using System.Collections.Immutable;

namespace Cpp2CS.Model;

// 泛型实参和 IR 操作数按内容比较，不使用数组引用作为身份。
public sealed class Sequence<T> : IReadOnlyList<T>, IEquatable<Sequence<T>>
{
    private readonly ImmutableArray<T> items;
    public Sequence(IEnumerable<T> items) => this.items = [.. items];
    public static Sequence<T> Of(params T[] items) => new(items);
    public int Count => items.Length;
    public T this[int index] => items[index];
    public bool Equals(Sequence<T>? other) => other is not null && items.SequenceEqual(other.items);
    public override bool Equals(object? obj) => obj is Sequence<T> other && Equals(other);
    public override int GetHashCode()
    {
        var hash = new HashCode();
        foreach (var item in items) hash.Add(item);
        return hash.ToHashCode();
    }
    public IEnumerator<T> GetEnumerator() => ((IEnumerable<T>)items).GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
