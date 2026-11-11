using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.Flow;

/// <summary>快照改写的区域凭据：单入口、指定出口、无环。拓扑顺序供改写者处理边上的定义。</summary>
public sealed record SnapshotRegion(ImmutableArray<BlockIdentity> Order);
public sealed class SnapshotRegionQuery(FlowQueries flow) : Query<BlockPair, SnapshotRegion>
{
    public override Outcome<SnapshotRegion> Compute(QueryContext c, BlockPair key)
    {
        Outcome<SnapshotRegion> Fail(string code, string text) => Outcome<SnapshotRegion>.Failure(new Reason(code, text));
        var graph = c.Get(flow.Graph, 0); if (!graph.IsSuccess) return graph.Propagate<SnapshotRegion>();
        var g = graph.Value;
        if (key.A == key.B) return Fail("structure.no-join", "入口与出口相同。");
        // 区域从终结之后开始；入口块中此前调用的异常出口不属于区域。
        var successors = SnapshotRewrite.Targets(c.Snapshot.Blocks.Single(b => b.Identity == key.A).End).Distinct().ToArray();
        foreach (var successor in successors)
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
            if (g.Successors[b].IsEmpty) return Fail("structure.other-exit", "区域有其他结局。");
            foreach (var next in g.Successors[b]) pending.Push(next);
        }
        foreach (var (from, targets) in g.Successors)
            if (from != key.A && !region.Contains(from) && targets.Any(region.Contains))
                return Fail("structure.shared-region", "区域有外部入口。");
        var degrees = region.ToDictionary(b => b, _ => 0);
        foreach (var b in region) foreach (var next in g.Successors[b]) if (region.Contains(next)) degrees[next]++;
        var queue = new Queue<BlockIdentity>(degrees.Where(p => p.Value == 0).Select(p => p.Key));
        var order = ImmutableArray.CreateBuilder<BlockIdentity>();
        while (queue.TryDequeue(out var b))
        {
            order.Add(b);
            foreach (var next in g.Successors[b]) if (region.Contains(next) && --degrees[next] == 0) queue.Enqueue(next);
        }
        return order.Count != region.Count ? Fail("structure.cycle", "区域含循环，不能消去终止性差异。")
            : Outcome<SnapshotRegion>.Success(new(order.ToImmutable()));
    }
}
