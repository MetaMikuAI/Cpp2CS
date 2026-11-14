using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;

namespace Cpp2CS.Kernel.Flow;

public readonly record struct BlockPair(BlockIdentity A, BlockIdentity B);
public readonly record struct PointPair(Point A, Point B);
public sealed record FlowGraph(ImmutableDictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>> Successors,
    ImmutableHashSet<BlockIdentity> Reachable, ImmutableHashSet<BlockIdentity> Exits);
public sealed class FlowGraphQuery(bool includeUnwind = true) : Query<int, FlowGraph>
{
    public override Outcome<FlowGraph> Compute(QueryContext c, int key)
    {
        var edges = c.Snapshot.Blocks.ToImmutableDictionary(b => b.Identity, b =>
        {
            IEnumerable<BlockIdentity> normal = b.End switch
            {
                Jump j => [j.Target], Branch t => [t.True, t.False],
                JumpTable t => t.Cases.Select(x => x.Target).Append(t.Default), _ => []
            };
            return normal.Concat(b.Statements.OfType<Call>().Where(_ => includeUnwind).Where(x => x.Unwind is not null).Select(x => x.Unwind!)).ToImmutableHashSet();
        });
        var seen = new HashSet<BlockIdentity>(); var pending = new Stack<BlockIdentity>(); pending.Push(c.Snapshot.Entry);
        while (pending.TryPop(out var b))
        {
            if (!seen.Add(b)) continue;
            if (c.Step() is { } why) return Outcome<FlowGraph>.Failure(why);
            foreach (var next in edges[b]) pending.Push(next);
        }
        // 没有本地处理入口的调用可能向外展开；没有效果证据时保留该出口。
        var exits = c.Snapshot.Blocks.Where(b => b.End is Return or ResumeUnwind or Unreachable ||
            b.Statements.Any(s => s is Call { DoesNotReturn: true } || includeUnwind && (s is TrapWhen or Call { Unwind: null }))).Select(b => b.Identity).ToImmutableHashSet();
        return Outcome<FlowGraph>.Success(new(edges, seen.ToImmutableHashSet(), exits));
    }
}

/// <summary>支配对入口可达块定义，含自支配；后支配对到达出口的有限路径定义；没有可达出口的块只承认自后支配。</summary>
public sealed class BlockDominanceQuery(FlowGraphQuery graph, bool post = false) : Query<BlockPair, bool>
{
    public override Outcome<bool> Compute(QueryContext c, BlockPair key)
    {
        var result = c.Get(graph, 0); if (!result.IsSuccess) return result.Propagate<bool>();
        var g = result.Value;
        if (!g.Reachable.Contains(key.A) || !g.Reachable.Contains(key.B)) return Outcome<bool>.Success(false);
        if (key.A == key.B) return Outcome<bool>.Success(true);
        if (!post)
        {
            var seen = new HashSet<BlockIdentity>(); var pending = new Stack<BlockIdentity>(); pending.Push(c.Snapshot.Entry);
            while (pending.TryPop(out var b))
            {
                if (b == key.A || !seen.Add(b)) continue;
                if (b == key.B) return Outcome<bool>.Success(false);
                if (c.Step() is { } why) return Outcome<bool>.Failure(why);
                foreach (var next in g.Successors[b]) pending.Push(next);
            }
            return Outcome<bool>.Success(true);
        }
        Outcome<bool> ReachesExit(bool avoid)
        {
            var seen = new HashSet<BlockIdentity>(); var pending = new Stack<BlockIdentity>(); pending.Push(key.B);
            while (pending.TryPop(out var b))
            {
                if ((avoid && b == key.A) || !seen.Add(b)) continue;
                if (g.Exits.Contains(b)) return Outcome<bool>.Success(true);
                if (c.Step() is { } why) return Outcome<bool>.Failure(why);
                foreach (var next in g.Successors[b]) pending.Push(next);
            }
            return Outcome<bool>.Success(false);
        }
        var exits = ReachesExit(false); if (!exits.IsSuccess || !exits.Value) return exits;
        var bypass = ReachesExit(true); return bypass.IsSuccess ? Outcome<bool>.Success(!bypass.Value) : bypass;
    }
}

/// <summary>复用原生出口检查的程序点支配；展开调用后的点不支配处理入口。</summary>
public sealed class PointDominanceQuery(BlockDominanceQuery blocks) : Query<PointPair, bool>
{
    private sealed class DominanceQuery : Query<int, Dominance>
    {
        public override Outcome<Dominance> Compute(QueryContext c, int key) => Outcome<Dominance>.Success(new(c.Snapshot));
    }
    private readonly DominanceQuery dominance = new();
    public override Outcome<bool> Compute(QueryContext c, PointPair key)
    {
        foreach (var p in new[] { key.A, key.B })
        {
            var block = c.Snapshot.Blocks.SingleOrDefault(b => b.Identity == p.Block);
            if (block is null || p.Before < 0 || p.Before > block.Statements.Length)
                return Outcome<bool>.Failure(new("flow.point", "程序点不属于快照。"));
        }
        foreach (var point in new[] { key.A, key.B })
        {
            var reachable = c.Get(blocks, new(point.Block, point.Block));
            if (!reachable.IsSuccess) return reachable;
            if (!reachable.Value) return Outcome<bool>.Success(false);
        }
        var result = c.Get(dominance, 0);
        return result.IsSuccess ? Outcome<bool>.Success(result.Value.StrictlyDominates(
            key.A.Block, key.A.Before, key.B.Block, key.B.Before)) : result.Propagate<bool>();
    }
}
public sealed class FlowQueries
{
    public FlowGraphQuery Graph { get; }
    public BlockDominanceQuery Dominates { get; }
    public BlockDominanceQuery PostDominates { get; }
    public PointDominanceQuery PointDominates { get; }
    public FlowQueries(bool includeUnwind = true) { Graph = new(includeUnwind); Dominates = new(Graph); PostDominates = new(Graph, true); PointDominates = new(Dominates); }
}
