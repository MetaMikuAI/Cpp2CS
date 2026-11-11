using System.Collections.Immutable;

namespace Cpp2CS.Kernel.State;

/// <summary>位来源通常为空或单项；只有多来源合流才分配不可变集合。</summary>
public readonly struct BitSourceSet
{
    private readonly BitSource single;
    private readonly ImmutableHashSet<BitSource>? many;
    public static BitSourceSet Empty => default;
    public BitSourceSet(BitSource source) { single = source; many = null; }
    private BitSourceSet(ImmutableHashSet<BitSource> sources) { single = default; many = sources; }
    public int Count => many?.Count ?? (single.Value is null ? 0 : 1);
    public bool IsEmpty => Count == 0;
    public BitSource Single() => Count == 1 ? single : throw new InvalidOperationException("位来源不是单项。");
    public bool Contains(BitSource value) => many?.Contains(value) ?? single.Value is not null && single == value;
    public bool Same(BitSourceSet other) => many is null && other.many is null ? single == other.single
        : many is not null && ReferenceEquals(many, other.many);
    public BitSourceSet Add(BitSource value)
    {
        if (IsEmpty) return new(value);
        if (Contains(value)) return this;
        return new((many ?? ImmutableHashSet.Create(single)).Add(value));
    }
    public BitSourceSet Union(BitSourceSet other)
    {
        if (other.IsEmpty || Same(other)) return this;
        if (IsEmpty) return other;
        if (other.many is null) return Add(other.single);
        if (many is null) return other.Add(single);
        var joined = many.Union(other.many);
        return ReferenceEquals(joined, many) ? this : new(joined);
    }
    public bool IsSubsetOf(BitSourceSet other)
    {
        if (IsEmpty || Same(other)) return true;
        if (Count > other.Count) return false;
        if (many is null) return other.Contains(single);
        foreach (var value in many) if (!other.Contains(value)) return false;
        return true;
    }
}
