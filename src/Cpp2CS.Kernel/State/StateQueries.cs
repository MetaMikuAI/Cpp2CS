using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.State;

public readonly record struct Point(BlockIdentity Block, int Before);
public readonly record struct StateKey(Point Point, Location Location);
public sealed record MemoryAtom(Location Location, StableIdentity? Definition) : AtomIdentity
{ public override string StableText => "state.memory"; }
public sealed record MemoryMerge(BlockIdentity Block, Location Location) : AtomIdentity
{ public override string StableText => "state.merge"; }
public sealed record MergeEdge(BlockIdentity Predecessor, int Before, Term Value);
public sealed record StateIndex(ImmutableDictionary<BlockIdentity, Block> Blocks,
    ImmutableDictionary<BlockIdentity, ImmutableArray<Point>> Predecessors,
    ImmutableDictionary<ReadIdentity, (Point Point, MemoryRead Read)> Reads);
public sealed class IndexQuery : Query<int, StateIndex>
{
    public override Outcome<StateIndex> Compute(QueryContext context, int key)
    {
        var f = context.Snapshot; var blocks = f.Blocks.ToImmutableDictionary(b => b.Identity);
        var predecessors = blocks.Keys.ToDictionary(b => b, _ => new List<Point>());
        var reads = ImmutableDictionary.CreateBuilder<ReadIdentity, (Point, MemoryRead)>();
        foreach (var b in f.Blocks)
        {
            for (int i = 0; i < b.Statements.Length; i++)
            {
                if (b.Statements[i] is MemoryRead r) reads.Add(r.Identity, (new(b.Identity, i), r));
                if (b.Statements[i] is Call { Unwind: { } target }) predecessors[target].Add(new(b.Identity, i + 1));
            }
            IEnumerable<BlockIdentity> targets = b.End switch
            {
                Jump j => [j.Target], Branch t => [t.True, t.False],
                JumpTable t => t.Cases.Select(c => c.Target).Append(t.Default), _ => []
            };
            foreach (var target in targets.Distinct()) predecessors[target].Add(new(b.Identity, b.Statements.Length));
        }
        return Outcome<StateIndex>.Success(new(blocks, predecessors.ToImmutableDictionary(p => p.Key, p => p.Value.ToImmutableArray()), reads.ToImmutable()));
    }
}

/// <summary>每一位的到达来源集合按包含关系增长；来源是有限的写入位或改写原子。</summary>
public readonly record struct BitSource(Term Value, int Bit);
public sealed record ReachingBits(ImmutableArray<BitSourceSet> Bits);
internal sealed class BitsLattice(int width) : ILattice<ReachingBits>
{
    private static readonly ImmutableArray<BitsLattice> common = Enumerable.Range(1, 128).Select(w => new BitsLattice(w)).ToImmutableArray();
    public static BitsLattice ForWidth(int width) => width is > 0 and <= 128 ? common[width - 1] : new(width);
    public ReachingBits Bottom { get; } = new(ImmutableArray.CreateRange(new BitSourceSet[width]));
    // 单项直接比较；多项集合沿用不可变实例，未增长时不分配。
    public ReachingBits Join(ReachingBits a, ReachingBits b)
    {
        if (ReferenceEquals(a, Bottom) || ReferenceEquals(a, b)) return b;
        ImmutableArray<BitSourceSet>.Builder? changed = null;
        for (int i = 0; i < a.Bits.Length; i++)
        {
            var value = a.Bits[i].Same(b.Bits[i]) ? a.Bits[i] : a.Bits[i].Union(b.Bits[i]);
            if (value.Same(a.Bits[i])) continue;
            changed ??= a.Bits.ToBuilder(); changed[i] = value;
        }
        return changed is null ? a : new(changed.ToImmutable());
    }
    public bool LessOrEqual(ReachingBits a, ReachingBits b)
    {
        if (ReferenceEquals(a, Bottom) || ReferenceEquals(a, b)) return true;
        for (int i = 0; i < a.Bits.Length; i++) if (!a.Bits[i].IsSubsetOf(b.Bits[i])) return false;
        return true;
    }
}

/// <summary>查询实例可供多个快照复用；上下文必须登记 Group。</summary>
public sealed class StateQueries
{
    public LocationQuery Locations { get; } = new();
    public EscapeQuery Escapes { get; }
    public AliasQuery Alias { get; }
    public CallEffectQuery Effects { get; }
    public IndexQuery Index { get; } = new();
    internal OutgoingExtentQuery OutgoingExtent { get; }
    public ReachingQuery Reaching { get; }
    public BitSourcesQuery BitSources { get; }
    public BitRangeSourcesQuery BitRanges { get; }
    public ValueAtQuery ValueAt { get; }
    public ReadQuery Read { get; }
    public ResolveQuery Resolve { get; }
    public MergeInputsQuery MergeInputs { get; }
    public CallerUsesQuery CallerUses { get; }
    public FixedPointGroup Group { get; }
    /// <summary>映像里不变的数据；没有给出映像时，映像位置的读取一律按普通内存处理。</summary>
    public ImageContents? Contents { get; }
    public StateQueries(ICallEffectSource? effects = null, long stepLimit = 10_000_000, Cpp2CS.Native.Images.IImage? image = null)
    {
        Contents = image is null ? null : ImageContents.Of(image);
        OutgoingExtent = new(Locations);
        Escapes = new(Locations); Alias = new(Escapes); Effects = new(effects ?? new UnknownCallEffects());
        Reaching = new(this); BitSources = new(this); BitRanges = new(this); ValueAt = new(this); Read = new(this); Resolve = new(this); MergeInputs = new(this); CallerUses = new(this);
        Group = new(stepLimit, FixedPointMember.Create(Reaching, k => BitsLattice.ForWidth(k.Location.Width)),
            FixedPointMember.Create(BitRanges, k => BitsLattice.ForWidth(k.Width)));
    }
    public QueryContext CreateContext(NativeFunction function) => new(function, null, Group);

    internal Outcome<(Term? Value, Overlap Overlap)> Definition(QueryContext c, Statement statement, Location location)
    {
        if (statement is MemoryWrite w)
        {
            var l = c.Get(Locations, new(w.Address, w.Width)); if (!l.IsSuccess) return l.Propagate<(Term?, Overlap)>();
            var a = c.Get(Alias, new(location, l.Value)); if (!a.IsSuccess) return a.Propagate<(Term?, Overlap)>();
            if (a.Value.Kind == AliasKind.Unknown) return Clobber(c, location, w.Identity);
            return Outcome<(Term?, Overlap)>.Success((w.Value, a.Value));
        }
        if (statement is not Call call) return Outcome<(Term?, Overlap)>.Success((null, new(AliasKind.Disjoint)));
        var effects = c.Get(Effects, call.Identity); if (!effects.IsSuccess) return effects.Propagate<(Term?, Overlap)>();
        foreach (var written in effects.Value.Writes)
        {
            var a = c.Get(Alias, new(location, written)); if (!a.IsSuccess) return a.Propagate<(Term?, Overlap)>();
            if (a.Value.Kind != AliasKind.Disjoint) return Clobber(c, location, call.Identity);
        }
        if (effects.Value.UnknownMemory)
        {
            if (location.Region is Region.Other or Region.Image or Region.Thread) return Clobber(c, location, call.Identity);
            var escapes = c.Get(Escapes, 0); if (!escapes.IsSuccess) return escapes.Propagate<(Term?, Overlap)>();
            if (escapes.Value.MayReach(location)) return Clobber(c, location, call.Identity);
        }
        if (call.OutgoingArgumentArea is { } area)
        {
            var start = c.Get(Locations, new(area, 1)); if (!start.IsSuccess) return start.Propagate<(Term?, Overlap)>();
            if (start.Value.Offset is null) return Clobber(c, location, call.Identity);
            var size = effects.Value.StackArgumentBytes;
            if (size is null)
            {
                var extent = c.Get(OutgoingExtent, start.Value);
                if (!extent.IsSuccess) return extent.Propagate<(Term?, Overlap)>();
                size = extent.Value;
            }
            if (size < 0 || size > int.MaxValue / 8) return Outcome<(Term?, Overlap)>.Failure(new("state.call-area", "栈实参区大小无法表示。"));
            if (size > 0)
            {
                var a = c.Get(Alias, new(location, start.Value with { Width = (int)size * 8 }));
                if (!a.IsSuccess) return a.Propagate<(Term?, Overlap)>();
                if (a.Value.Kind != AliasKind.Disjoint) return Clobber(c, location, call.Identity);
            }
        }
        return Outcome<(Term?, Overlap)>.Success((null, new(AliasKind.Disjoint)));
    }
    private static Outcome<(Term?, Overlap)> Clobber(QueryContext c, Location l, StableIdentity id) =>
        Outcome<(Term?, Overlap)>.Success((c.Snapshot.Terms.Atom(new MemoryAtom(l, id), l.Width), new(AliasKind.Overlap, 0, 0, l.Width)));
}

/// <summary>同一快照与区域起点的未知栈实参区上界只扫描一次；与被查询的读取位置无关。</summary>
internal sealed class OutgoingExtentQuery(LocationQuery locations) : Query<Location, BigInteger>
{
    public override Outcome<BigInteger> Compute(QueryContext c, Location key)
    {
        // 连续的直接写入槽给出未知栈实参区的上界。
        var end = key.Offset!.Value * 8;
        var slots = new List<Location>();
        foreach (var write in c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>())
        {
            var location = c.Get(locations, new(write.Address, write.Width));
            if (!location.IsSuccess) return location.Propagate<BigInteger>();
            if (location.Value.Root == key.Root && location.Value.Offset is not null) slots.Add(location.Value);
        }
        foreach (var slot in slots.OrderBy(s => s.Offset))
            if (slot.Offset * 8 <= end && slot.Offset * 8 + slot.Width > end) end = slot.Offset!.Value * 8 + slot.Width;
        return Outcome<BigInteger>.Success((end - key.Offset.Value * 8 + 7) / 8);
    }
}

public sealed class ReachingQuery(StateQueries q) : Query<StateKey, ReachingBits>
{
    public override Outcome<ReachingBits> Compute(QueryContext c, StateKey key)
    {
        var index = c.Get(q.Index, 0); if (!index.IsSuccess) return index.Propagate<ReachingBits>();
        var block = index.Value.Blocks[key.Point.Block]; var t = c.Snapshot.Terms;
        var bits = new BitSourceSet[key.Location.Width];
        var assigned = new bool[bits.Length];
        for (int i = key.Point.Before - 1; i >= 0; i--)
        {
            if (c.Step() is { } why) return Outcome<ReachingBits>.Failure(why);
            var d = q.Definition(c, block.Statements[i], key.Location); if (!d.IsSuccess) return d.Propagate<ReachingBits>();
            var (value, overlap) = d.Value;
            if (overlap.Kind == AliasKind.Disjoint) continue;
            for (int j = 0; j < overlap.Width;)
            {
                if (assigned[overlap.LeftLow + j]) { j++; continue; }
                int end = j + 1;
                while (end < overlap.Width && !assigned[overlap.LeftLow + end]) end++;
                var sources = c.Get(q.BitRanges, new(value!, overlap.RightLow + j, end - j));
                if (!sources.IsSuccess) return sources.Propagate<ReachingBits>();
                for (int k = j; k < end; k++)
                { assigned[overlap.LeftLow + k] = true; bits[overlap.LeftLow + k] = sources.Value.Bits[k - j]; }
                j = end;
            }
            if (assigned.All(v => v)) return Outcome<ReachingBits>.Success(new(bits.ToImmutableArray()));
        }
        var predecessors = index.Value.Predecessors[block.Identity];
        if (block.Identity == c.Snapshot.Entry || predecessors.IsEmpty)
        {
            var entry = t.Atom(new MemoryAtom(key.Location, null), bits.Length);
            for (int i = 0; i < bits.Length; i++) if (!assigned[i]) bits[i] = bits[i].Add(new(entry, i));
        }
        foreach (var p in predecessors)
        {
            var previous = c.Get(this, new(p, key.Location)); if (!previous.IsSuccess) return previous;
            for (int i = 0; i < bits.Length; i++)
                if (!assigned[i] && !bits[i].Same(previous.Value.Bits[i])) bits[i] = bits[i].Union(previous.Value.Bits[i]);
        }
        return Outcome<ReachingBits>.Success(new(bits.ToImmutableArray()));
    }
}

public sealed class ValueAtQuery(StateQueries q) : Query<StateKey, Term>
{
    public override Outcome<Term> Compute(QueryContext c, StateKey key)
    {
        if (q.Contents?.Read(c.Snapshot, key.Location) is { } constant) return Outcome<Term>.Success(constant);
        var reaching = c.Get(q.Reaching, key); if (!reaching.IsSuccess) return reaching.Propagate<Term>();
        if (reaching.Value.Bits.Any(s => s.IsEmpty)) return Outcome<Term>.Failure(new("state.unreachable-cycle", "位置没有可达的入口定义。"));
        var t = c.Snapshot.Terms;
        if (reaching.Value.Bits.All(s => s.Count == 1))
        {
            var sources = reaching.Value.Bits.Select(s => s.Single()).ToArray();
            var pieces = new List<Term>();
            for (int i = 0; i < sources.Length;)
            {
                int end = i + 1;
                while (end < sources.Length && sources[end].Value == sources[i].Value && sources[end].Bit == sources[i].Bit + end - i) end++;
                pieces.Add(t.Slice(sources[i].Value, sources[i].Bit, end - i)); i = end;
            }
            return c.Get(q.Resolve, t.Concat(pieces.ToArray()));
        }
        var index = c.Get(q.Index, 0); if (!index.IsSuccess) return index.Propagate<Term>();
        var block = index.Value.Blocks[key.Point.Block];
        // 不相交的语句不改变读取值；一次跳过，避免每退一步都重建整个位来源查询。
        for (int i = key.Point.Before - 1; i >= 0; i--)
        {
            if (c.Step() is { } why) return Outcome<Term>.Failure(why);
            var d = q.Definition(c, block.Statements[i], key.Location); if (!d.IsSuccess) return d.Propagate<Term>();
            if (d.Value.Overlap.Kind == AliasKind.Disjoint) continue;
            var prior = new StateKey(key.Point with { Before = i }, key.Location);
            var overlap = d.Value.Overlap;
            var written = c.Get(q.Resolve, t.Slice(d.Value.Value!, overlap.RightLow, overlap.Width)); if (!written.IsSuccess) return written;
            if (overlap.Width == key.Location.Width) return written;
            var previous = c.Get(this, prior); if (!previous.IsSuccess) return previous;
            var parts = new List<Term>();
            if (overlap.LeftLow > 0) parts.Add(t.Slice(previous.Value, 0, overlap.LeftLow));
            parts.Add(written.Value);
            var high = overlap.LeftLow + overlap.Width;
            if (high < key.Location.Width) parts.Add(t.Slice(previous.Value, high, key.Location.Width - high));
            return Outcome<Term>.Success(t.Concat(parts.ToArray()));
        }
        var predecessors = index.Value.Predecessors[block.Identity];
        if (predecessors.Length == 1) return c.Get(this, new(predecessors[0], key.Location));
        return Outcome<Term>.Success(t.Atom(new MemoryMerge(block.Identity, key.Location), key.Location.Width));
    }
}
public sealed class ReadQuery(StateQueries q) : Query<ReadIdentity, Term>
{
    public override Outcome<Term> Compute(QueryContext c, ReadIdentity key)
    {
        var index = c.Get(q.Index, 0); if (!index.IsSuccess) return index.Propagate<Term>();
        if (!index.Value.Reads.TryGetValue(key, out var read)) return Outcome<Term>.Failure(new("state.read", "快照中没有该读取。"));
        var address = c.Get(q.Resolve, read.Read.Address); if (!address.IsSuccess) return address;
        var location = c.Get(q.Locations, new(address.Value, read.Read.Width)); if (!location.IsSuccess) return location.Propagate<Term>();
        return c.Get(q.ValueAt, new(read.Point, location.Value));
    }
}
public sealed class ResolveQuery(StateQueries q) : Query<Term, Term>
{
    public override Outcome<Term> Compute(QueryContext c, Term key)
    {
        if (key.Identity is ResultAtom { Definition: ReadIdentity id }) return c.Get(q.Read, id);
        if (key.Operands.IsEmpty) return Outcome<Term>.Success(key);
        var operands = new Term[key.Operands.Length];
        for (int i = 0; i < operands.Length; i++)
        { var v = c.Get(this, key.Operands[i]); if (!v.IsSuccess) return v; operands[i] = v.Value; }
        var t = c.Snapshot.Terms;
        return Outcome<Term>.Success(key.Kind switch
        { TermKind.Slice => t.Slice(operands[0], key.SliceLow!.Value, key.Width), TermKind.Concat => t.Concat(operands),
            TermKind.Operation => t.Apply(key.Operator!, key.Width, operands), _ => key });
    }
}
public sealed class MergeInputsQuery(StateQueries q) : Query<MemoryMerge, ImmutableArray<MergeEdge>>
{
    public override Outcome<ImmutableArray<MergeEdge>> Compute(QueryContext c, MemoryMerge key)
    {
        var index = c.Get(q.Index, 0); if (!index.IsSuccess) return index.Propagate<ImmutableArray<MergeEdge>>();
        var values = ImmutableArray.CreateBuilder<MergeEdge>();
        foreach (var p in index.Value.Predecessors[key.Block])
        {
            var v = c.Get(q.ValueAt, new(p, key.Location)); if (!v.IsSuccess) return v.Propagate<ImmutableArray<MergeEdge>>();
            values.Add(new(p.Block, p.Before, v.Value));
        }
        return Outcome<ImmutableArray<MergeEdge>>.Success(values.ToImmutable());
    }
}

public readonly record struct BitRequest(Term Value, int Bit);
/// <summary>单个位查询是批量位来源的视图；不在组外读取尚未收敛的近似值。</summary>
public sealed class BitSourcesQuery(StateQueries q) : Query<BitRequest, BitSourceSet>
{
    public override Outcome<BitSourceSet> Compute(QueryContext c, BitRequest key)
    {
        var range = c.Get(q.BitRanges, new(key.Value, key.Bit, 1));
        return range.IsSuccess ? Outcome<BitSourceSet>.Success(range.Value.Bits[0]) : range.Propagate<BitSourceSet>();
    }
}
public readonly record struct BitRangeRequest(Term Value, int Low, int Width);
/// <summary>一段位共用依赖边；只访问请求范围，避免无关位的失败影响结果。</summary>
public sealed class BitRangeSourcesQuery(StateQueries q) : Query<BitRangeRequest, ReachingBits>
{
    public override Outcome<ReachingBits> Compute(QueryContext c, BitRangeRequest key)
    {
        var term = key.Value;
        if (key.Low < 0 || key.Width <= 0 || key.Low > term.Width - key.Width)
            return Outcome<ReachingBits>.Failure(new("state.bit-range", "位来源范围超出值的宽度。"));
        if (term.Kind == TermKind.Slice) return c.Get(this, new(term.Operands[0], key.Low + term.SliceLow!.Value, key.Width));
        if (term.Kind == TermKind.Concat)
        {
            var bits = ImmutableArray.CreateBuilder<BitSourceSet>(key.Width); int offset = 0;
            foreach (var part in term.Operands)
            {
                int low = Math.Max(key.Low, offset), end = Math.Min(key.Low + key.Width, offset + part.Width);
                if (low < end)
                {
                    var range = c.Get(this, new(part, low - offset, end - low));
                    if (!range.IsSuccess) return range;
                    bits.AddRange(range.Value.Bits);
                }
                offset += part.Width;
            }
            return Outcome<ReachingBits>.Success(new(bits.MoveToImmutable()));
        }
        if (term.Identity is ResultAtom { Definition: ReadIdentity id })
        {
            var index = c.Get(q.Index, 0); if (!index.IsSuccess) return index.Propagate<ReachingBits>();
            var read = index.Value.Reads[id];
            var l = c.Get(q.Locations, new(read.Read.Address, read.Read.Width)); if (!l.IsSuccess) return l.Propagate<ReachingBits>();
            var reaching = c.Get(q.Reaching, new(read.Point, l.Value));
            if (!reaching.IsSuccess) return reaching;
            return Outcome<ReachingBits>.Success(new(reaching.Value.Bits.Slice(key.Low, key.Width)));
        }
        var result = ImmutableArray.CreateBuilder<BitSourceSet>(key.Width);
        for (int i = 0; i < key.Width; i++) result.Add(new(new(term, key.Low + i)));
        return Outcome<ReachingBits>.Success(new(result.MoveToImmutable()));
    }
}
