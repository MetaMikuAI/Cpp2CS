using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;

namespace Cpp2CS.Kernel.Flow;

public readonly record struct BlockPair(BlockIdentity A, BlockIdentity B);
public readonly record struct PointPair(Point A, Point B);
public sealed record FlowGraph(ImmutableDictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>> Successors,
    ImmutableHashSet<BlockIdentity> Reachable, ImmutableHashSet<BlockIdentity> Exits);
public sealed class FlowGraphQuery : Query<int, FlowGraph>
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
            return normal.Concat(b.Statements.OfType<Call>().Where(x => x.Unwind is not null).Select(x => x.Unwind!)).ToImmutableHashSet();
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
            b.Statements.Any(s => s is TrapWhen or Call { DoesNotReturn: true } or Call { Unwind: null })).Select(b => b.Identity).ToImmutableHashSet();
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

/// <summary>同块严格按语句次序；不同块使用严格块支配。Before 使用状态模型的程序点编号。</summary>
public sealed class PointDominanceQuery(BlockDominanceQuery blocks) : Query<PointPair, bool>
{
    public override Outcome<bool> Compute(QueryContext c, PointPair key)
    {
        foreach (var p in new[] { key.A, key.B })
        {
            var block = c.Snapshot.Blocks.SingleOrDefault(b => b.Identity == p.Block);
            if (block is null || p.Before < 0 || p.Before > block.Statements.Length)
                return Outcome<bool>.Failure(new("flow.point", "程序点不属于快照。"));
        }
        return key.A.Block == key.B.Block ? Outcome<bool>.Success(key.A.Before < key.B.Before)
            : c.Get(blocks, new(key.A.Block, key.B.Block));
    }
}
public sealed class FlowQueries
{
    public FlowGraphQuery Graph { get; } = new();
    public BlockDominanceQuery Dominates { get; }
    public BlockDominanceQuery PostDominates { get; }
    public PointDominanceQuery PointDominates { get; }
    public FlowQueries() { Dominates = new(Graph); PostDominates = new(Graph, true); PointDominates = new(Dominates); }
}
