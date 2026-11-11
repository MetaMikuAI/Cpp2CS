using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;

namespace Cpp2CS.Kernel.Flow;

public readonly record struct FlowEdge(BlockIdentity Source, BlockIdentity Target);
public readonly record struct FrontierStart(Point Point, FlowEdge? Edge = null)
{
    public static FrontierStart FromEdge(FlowEdge edge) => new(new(edge.Target, 0), edge);
}
public sealed record EventFrontier(ImmutableHashSet<Point> Stops, bool ReachesExit, bool HasCycle);

/// <summary>停点判定包含终结前的位置（Before 等于语句数）。不解释停点的语义；回边与已完成的合流分开处理。</summary>
public sealed class EventFrontierQuery(Func<QueryContext, Point, Outcome<bool>> stop, long stepBudget = 1_000_000)
    : Query<FrontierStart, EventFrontier>(stepBudget)
{
    public override Outcome<EventFrontier> Compute(QueryContext c, FrontierStart key)
    {
        var blocks = c.Snapshot.Blocks.ToDictionary(b => b.Identity);
        if (!blocks.TryGetValue(key.Point.Block, out var first) || key.Point.Before < 0 || key.Point.Before > first.Statements.Length)
            return Outcome<EventFrontier>.Failure(new("flow.point", "程序点不属于快照。"));
        if (key.Edge is { } edge && (key.Point != new Point(edge.Target, 0) || !blocks.TryGetValue(edge.Source, out var source) ||
            !Targets(source.End).Concat(source.Statements.OfType<Call>().Where(x => x.Unwind is not null).Select(x => x.Unwind!)).Contains(edge.Target)))
            return Outcome<EventFrontier>.Failure(new("flow.edge", "边不属于快照。"));
        var stops = ImmutableHashSet.CreateBuilder<Point>(); bool exits = false, cycle = false;
        var colors = new Dictionary<BlockIdentity, int>();
        var work = new Stack<(Point Point, bool Leave)>(); work.Push((key.Point, false));
        while (work.TryPop(out var item))
        {
            if (c.Step() is { } why) return Outcome<EventFrontier>.Failure(why);
            var id = item.Point.Block;
            if (item.Leave) { colors[id] = 2; continue; }
            if (colors.TryGetValue(id, out var color)) { cycle |= color == 1; continue; }
            colors[id] = 1; work.Push((item.Point, true));
            var b = blocks[id]; bool ended = false;
            for (int i = item.Point.Before; i <= b.Statements.Length; i++)
            {
                if (c.Step() is { } step) return Outcome<EventFrontier>.Failure(step);
                var point = new Point(id, i); var result = stop(c, point);
                if (!result.IsSuccess) return result.Propagate<EventFrontier>();
                if (result.Value) { stops.Add(point); ended = true; break; }
                if (i == b.Statements.Length) break;
                if (b.Statements[i] is Call call)
                {
                    if (call.Unwind is { } handler) work.Push((new(handler, 0), false));
                    if (call.DoesNotReturn) { exits = true; ended = true; break; }
                }
                if (b.Statements[i] is TrapWhen) exits = true;
            }
            if (ended) continue;
            var targets = Targets(b.End).Distinct().ToArray();
            if (targets.Length == 0) exits = true;
            foreach (var target in targets) work.Push((new(target, 0), false));
        }
        return Outcome<EventFrontier>.Success(new(stops.ToImmutable(), exits, cycle));
    }
    private static IEnumerable<BlockIdentity> Targets(Terminator end) => end switch
    {
        Jump j => [j.Target], Branch b => [b.True, b.False],
        JumpTable t => t.Cases.Select(x => x.Target).Append(t.Default), _ => []
    };
}
