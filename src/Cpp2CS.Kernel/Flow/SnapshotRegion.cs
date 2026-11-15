using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.Flow;

/// <summary>快照改写的区域凭据：单入口、指定出口、无环。拓扑顺序供改写者处理边上的定义。</summary>
public sealed record SnapshotRegion(ImmutableArray<BlockIdentity> Order);
public sealed class SnapshotRegionQuery(FlowQueries flow, Query<FlowEdge, bool>? failureExits = null) : Query<BlockPair, SnapshotRegion>
{
    private readonly RegionEdges edges = new(flow, failureExits);
    private sealed class RegionEdges(FlowQueries flow, Query<FlowEdge, bool>? failureExits)
        : Query<int, IReadOnlyDictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>>>
    {
        public override Outcome<IReadOnlyDictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>>> Compute(QueryContext c, int key)
        {
            var graph = c.Get(flow.Graph, 0);
            if (!graph.IsSuccess) return graph.Propagate<IReadOnlyDictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>>>();
            var g = graph.Value;
            var successorsByBlock = new Dictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>>();
            foreach (var (source, targets) in g.Successors)
            {
                var kept = ImmutableHashSet.CreateBuilder<BlockIdentity>();
                foreach (var target in targets)
                {
                    var excluded = failureExits is null ? Outcome<bool>.Success(false) : c.Get(failureExits, new(source, target));
                    if (!excluded.IsSuccess) return excluded.Propagate<IReadOnlyDictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>>>();
                    if (!excluded.Value) kept.Add(target);
                }
                successorsByBlock.Add(source, kept.ToImmutable());
            }
            return Outcome<IReadOnlyDictionary<BlockIdentity, ImmutableHashSet<BlockIdentity>>>.Success(successorsByBlock);
        }
    }
    public override Outcome<SnapshotRegion> Compute(QueryContext c, BlockPair key)
    {
        Outcome<SnapshotRegion> Fail(string code, string text) => Outcome<SnapshotRegion>.Failure(new Reason(code, text));
        var graph = c.Get(flow.Graph, 0); if (!graph.IsSuccess) return graph.Propagate<SnapshotRegion>();
        var g = graph.Value;
        var filtered = c.Get(edges, 0); if (!filtered.IsSuccess) return filtered.Propagate<SnapshotRegion>();
        var successorsByBlock = filtered.Value;
        if (key.A == key.B) return Fail("structure.no-join", "入口与出口相同。");
        // 区域从终结之后开始；入口块中此前调用的异常出口不属于区域。
        var successors = SnapshotRewrite.Targets(c.Snapshot.Blocks.Single(b => b.Identity == key.A).End).Where(successorsByBlock[key.A].Contains).Distinct().ToArray();
        if (successors.Length == 0) return Fail("structure.other-exit", "区域没有通向续点的正常出口。");
        foreach (var successor in successors.Where(_ => failureExits is null))
        {
            var post = c.Get(flow.PostDominates, new(key.B, successor));
            if (!post.IsSuccess) return post.Propagate<SnapshotRegion>();
            if (!post.Value) return Fail("structure.no-join", "出口不后支配分支后继。");
        }
        var region = new HashSet<BlockIdentity>(); var pending = new Stack<BlockIdentity>(successors);
        while (pending.TryPop(out var b))
        {
            if (b == key.B || !region.Add(b)) continue;
            if (c.Step() is { } why) return Outcome<SnapshotRegion>.Failure(why);
            if (b == key.A) return Fail("structure.cycle", "区域含回边。");
            if (successorsByBlock[b].IsEmpty) return Fail("structure.other-exit", "区域有其他结局。");
            foreach (var next in successorsByBlock[b]) pending.Push(next);
        }
        foreach (var (from, targets) in g.Successors)
            if (from != key.A && !region.Contains(from) && targets.Any(region.Contains))
                return Fail("structure.shared-region", "区域有外部入口。");
        var degrees = region.ToDictionary(b => b, _ => 0);
        foreach (var b in region) foreach (var next in successorsByBlock[b]) if (region.Contains(next)) degrees[next]++;
        var queue = new Queue<BlockIdentity>(degrees.Where(p => p.Value == 0).Select(p => p.Key));
        var order = ImmutableArray.CreateBuilder<BlockIdentity>();
        while (queue.TryDequeue(out var b))
        {
            order.Add(b);
            foreach (var next in successorsByBlock[b]) if (region.Contains(next) && --degrees[next] == 0) queue.Enqueue(next);
        }
        return order.Count != region.Count ? Fail("structure.cycle", "区域含循环，不能消去终止性差异。")
            : Outcome<SnapshotRegion>.Success(new(order.ToImmutable()));
    }
}


public sealed record SnapshotPath(ImmutableArray<Point> Points, ImmutableArray<FlowEdge> Edges);
public readonly record struct SnapshotPathKey(Point Entry, BlockIdentity Join);

/// <summary>在已证明的无环区域上展开完整路径；每个语句点和边均保留原身份。</summary>
public sealed class SnapshotPathsQuery(FlowQueries flow, Query<FlowEdge, bool>? failureExits = null, int pathBudget = 64)
    : Query<SnapshotPathKey, ImmutableArray<SnapshotPath>>
{
    private readonly SnapshotRegionQuery regions = new(flow, failureExits);
    public override Outcome<ImmutableArray<SnapshotPath>> Compute(QueryContext c, SnapshotPathKey key)
    {
        var area = c.Get(regions, new(key.Entry.Block, key.Join));
        if (!area.IsSuccess) return area.Propagate<ImmutableArray<SnapshotPath>>();
        var blocks = c.Snapshot.Blocks.ToDictionary(b => b.Identity);
        if (key.Entry.Before < 0 || key.Entry.Before > blocks[key.Entry.Block].Statements.Length)
            return Outcome<ImmutableArray<SnapshotPath>>.Failure(new("flow.point", "入口程序点不属于快照。"));
        var at = new Dictionary<BlockIdentity, List<SnapshotPath>> { [key.Entry.Block] = [new([], [])] };
        foreach (var id in area.Value.Order.Prepend(key.Entry.Block))
        {
            if (!at.TryGetValue(id, out var prefixes)) continue;
            var b = blocks[id]; int start = id == key.Entry.Block ? key.Entry.Before : 0;
            var points = Enumerable.Range(start, b.Statements.Length - start).Select(i => new Point(id, i)).ToArray();
            foreach (var target in SnapshotRewrite.Targets(b.End).Distinct())
            {
                var edge = new FlowEdge(id, target);
                var excluded = failureExits is null ? Outcome<bool>.Success(false) : c.Get(failureExits, edge);
                if (!excluded.IsSuccess) return excluded.Propagate<ImmutableArray<SnapshotPath>>();
                if (excluded.Value) continue;
                if (!at.TryGetValue(target, out var paths)) at.Add(target, paths = []);
                foreach (var prefix in prefixes)
                {
                    if (c.Step() is { } why) return Outcome<ImmutableArray<SnapshotPath>>.Failure(why);
                    if (paths.Count >= pathBudget) return Outcome<ImmutableArray<SnapshotPath>>.Failure(new("flow.path-budget", "区域路径数超过展开预算。"));
                    paths.Add(new([.. prefix.Points, .. points], [.. prefix.Edges, edge]));
                }
            }
        }
        return Outcome<ImmutableArray<SnapshotPath>>.Success(at.GetValueOrDefault(key.Join)?.ToImmutableArray() ?? []);
    }
}
