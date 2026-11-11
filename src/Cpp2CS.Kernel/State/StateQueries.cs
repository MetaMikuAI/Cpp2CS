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
public sealed record ReachingBits(ImmutableArray<ImmutableHashSet<BitSource>> Bits);
internal sealed class BitsLattice(int width) : ILattice<ReachingBits>
{
    public ReachingBits Bottom { get; } = new(Enumerable.Range(0, width).Select(_ => ImmutableHashSet<BitSource>.Empty).ToImmutableArray());
    public ReachingBits Join(ReachingBits a, ReachingBits b) => new(a.Bits.Select((s, i) => s.Union(b.Bits[i])).ToImmutableArray());
    public bool LessOrEqual(ReachingBits a, ReachingBits b) => a.Bits.Select((s, i) => s.IsSubsetOf(b.Bits[i])).All(v => v);
}

/// <summary>查询实例可供多个快照复用；上下文必须登记 Group。</summary>
public sealed class StateQueries
{
    public LocationQuery Locations { get; } = new();
    public EscapeQuery Escapes { get; }
    public AliasQuery Alias { get; }
    public CallEffectQuery Effects { get; }
    public IndexQuery Index { get; } = new();
    public ReachingQuery Reaching { get; }
    public BitSourcesQuery BitSources { get; }
    public ValueAtQuery ValueAt { get; }
    public ReadQuery Read { get; }
    public ResolveQuery Resolve { get; }
    public MergeInputsQuery MergeInputs { get; }
    public CallerUsesQuery CallerUses { get; }
    public FixedPointGroup Group { get; }
    public StateQueries(ICallEffectSource? effects = null, long stepLimit = 10_000_000)
    {
        Escapes = new(Locations); Alias = new(Escapes); Effects = new(effects ?? new UnknownCallEffects());
        Reaching = new(this); BitSources = new(this); ValueAt = new(this); Read = new(this); Resolve = new(this); MergeInputs = new(this); CallerUses = new(this);
        Group = new(stepLimit, FixedPointMember.Create(Reaching, k => new BitsLattice(k.Location.Width)),
            FixedPointMember.Create(BitSources, _ => new SourceLattice()));
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
                // 连续的直接写入槽给出未知栈实参区的上界。
                var end = start.Value.Offset.Value * 8;
                var slots = new List<Location>();
                foreach (var write in c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>())
                {
                    var l = c.Get(Locations, new(write.Address, write.Width)); if (!l.IsSuccess) return l.Propagate<(Term?, Overlap)>();
                    if (l.Value.Root == start.Value.Root && l.Value.Offset is not null) slots.Add(l.Value);
                }
                foreach (var slot in slots.OrderBy(s => s.Offset))
                    if (slot.Offset * 8 <= end && slot.Offset * 8 + slot.Width > end) end = slot.Offset!.Value * 8 + slot.Width;
                size = (end - start.Value.Offset.Value * 8 + 7) / 8;
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

public sealed class ReachingQuery(StateQueries q) : Query<StateKey, ReachingBits>
{
    public override Outcome<ReachingBits> Compute(QueryContext c, StateKey key)
    {
        var index = c.Get(q.Index, 0); if (!index.IsSuccess) return index.Propagate<ReachingBits>();
        var block = index.Value.Blocks[key.Point.Block]; var t = c.Snapshot.Terms;
        var bits = Enumerable.Range(0, key.Location.Width).Select(_ => ImmutableHashSet<BitSource>.Empty).ToArray();
        var assigned = new bool[bits.Length];
        for (int i = key.Point.Before - 1; i >= 0; i--)
        {
            if (c.Step() is { } why) return Outcome<ReachingBits>.Failure(why);
            var d = q.Definition(c, block.Statements[i], key.Location); if (!d.IsSuccess) return d.Propagate<ReachingBits>();
            var (value, overlap) = d.Value;
            if (overlap.Kind == AliasKind.Disjoint) continue;
            for (int j = 0; j < overlap.Width; j++)
            {
                var bit = overlap.LeftLow + j;
                if (assigned[bit]) continue;
                var sources = c.Get(q.BitSources, new(value!, overlap.RightLow + j));
                if (!sources.IsSuccess) return sources.Propagate<ReachingBits>();
                assigned[bit] = true; bits[bit] = sources.Value;
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
            for (int i = 0; i < bits.Length; i++) if (!assigned[i]) bits[i] = bits[i].Union(previous.Value.Bits[i]);
        }
        return Outcome<ReachingBits>.Success(new(bits.ToImmutableArray()));
    }
}

public sealed class ValueAtQuery(StateQueries q) : Query<StateKey, Term>
{
    public override Outcome<Term> Compute(QueryContext c, StateKey key)
    {
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
        if (key.Point.Before == 0)
        {
            var predecessors = index.Value.Predecessors[block.Identity];
            if (predecessors.Length == 1) return c.Get(this, new(predecessors[0], key.Location));
            return Outcome<Term>.Success(t.Atom(new MemoryMerge(block.Identity, key.Location), key.Location.Width));
        }
        var d = q.Definition(c, block.Statements[key.Point.Before - 1], key.Location); if (!d.IsSuccess) return d.Propagate<Term>();
        var prior = new StateKey(key.Point with { Before = key.Point.Before - 1 }, key.Location);
        if (d.Value.Overlap.Kind == AliasKind.Disjoint) return c.Get(this, prior);
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
internal sealed class SourceLattice : ILattice<ImmutableHashSet<BitSource>>
{
    public ImmutableHashSet<BitSource> Bottom => [];
    public ImmutableHashSet<BitSource> Join(ImmutableHashSet<BitSource> a, ImmutableHashSet<BitSource> b) => a.Union(b);
    public bool LessOrEqual(ImmutableHashSet<BitSource> a, ImmutableHashSet<BitSource> b) => a.IsSubsetOf(b);
}
/// <summary>纯位搬运穿透读取；运算仍是定义点的项，不沿循环展开表达式。</summary>
public sealed class BitSourcesQuery(StateQueries q) : Query<BitRequest, ImmutableHashSet<BitSource>>
{
    public override Outcome<ImmutableHashSet<BitSource>> Compute(QueryContext c, BitRequest key)
    {
        var term = key.Value; var bit = key.Bit;
        if (term.Kind == TermKind.Slice) return c.Get(this, new(term.Operands[0], bit + term.SliceLow!.Value));
        if (term.Kind == TermKind.Concat)
            foreach (var part in term.Operands)
            {
                if (bit < part.Width) return c.Get(this, new(part, bit));
                bit -= part.Width;
            }
        if (term.Identity is ResultAtom { Definition: ReadIdentity id })
        {
            var index = c.Get(q.Index, 0); if (!index.IsSuccess) return index.Propagate<ImmutableHashSet<BitSource>>();
            var read = index.Value.Reads[id];
            var l = c.Get(q.Locations, new(read.Read.Address, read.Read.Width)); if (!l.IsSuccess) return l.Propagate<ImmutableHashSet<BitSource>>();
            var reaching = c.Get(q.Reaching, new(read.Point, l.Value));
            if (!reaching.IsSuccess) return reaching.Propagate<ImmutableHashSet<BitSource>>();
            return Outcome<ImmutableHashSet<BitSource>>.Success(reaching.Value.Bits[bit]);
        }
        return Outcome<ImmutableHashSet<BitSource>>.Success([new(term, bit)]);
    }
}
