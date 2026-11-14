using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Inlining;

internal sealed record MergedAllocationRequest(BlockIdentity Block, Merge Merge);

/// <summary>同类新分配在无使用、无事件的前沿合流后，与现场的一次构造调用配对。</summary>
internal sealed class MergedAllocationConstructorQuery(StateQueries state, ManagedLocationQuery? locations, CallNamingQuery calls,
    IReadOnlyDictionary<CallIdentity, ConstructorCall> bindings, IReadOnlyDictionary<Term, AllocationConstructorRequest> allocations,
    ValueNamingQuery? names) : Query<MergedAllocationRequest, AllocationConstructorAnswer>
{
    private readonly AllocationConstructorQuery direct = new(state, locations, calls, bindings, null);
    internal FreshAllocationSourcesQuery Sources { get; } = new(state, allocations);
    private readonly ExistingMergeQuery existing = new(state);

    public override Outcome<AllocationConstructorAnswer> Compute(QueryContext c, MergedAllocationRequest key)
    {
        Outcome<AllocationConstructorAnswer> No(string code, string message, Reason? cause = null) =>
            Outcome<AllocationConstructorAnswer>.Success(new(null, null, new("lowering.Allocation.Merge." + code, message, cause)));
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<AllocationConstructorAnswer>();
        var block = index.Value.Blocks[key.Block]; var merge = key.Merge;
        if (merge.Result.Width != c.Snapshot.AddressWidth || merge.Inputs.IsEmpty || merge.Result.ContainsUndefined)
            return No("Input", "对象合流不是完整、有定义且有输入的引用。");
        var sourceValues = c.Get(Sources, merge.Result);
        if (!sourceValues.IsSuccess) return No("Input", sourceValues.Why!.Message, sourceValues.Why);
        var inputs = sourceValues.Value.Inputs;
        var uses = new SemanticUses(c, calls, state);
        var roots = uses.Roots.GroupBy(u => u.Point).ToDictionary(g => g.Key, g => g.ToArray());
        Outcome<bool> Uses(Point point, IReadOnlySet<Term> targets)
        {
            if (!roots.TryGetValue(point, out var at)) return Outcome<bool>.Success(false);
            foreach (var root in at)
            {
                var value = c.Get(state.Resolve, root.Value); if (!value.IsSuccess) return value.Propagate<bool>();
                bool found = false;
                uses.Visit(value.Value, (term, _, _) => found |= targets.Contains(term));
                if (found) return Outcome<bool>.Success(true);
            }
            return Outcome<bool>.Success(false);
        }
        var join = new Point(key.Block, 0);
        if (inputs.Any(i => !i.Type.Equals(inputs[0].Type)))
        {
            var target = new HashSet<Term> { merge.Result };
            var frontier = new EventFrontierQuery((_, p) => Uses(p, target));
            var reached = c.Get(frontier, new(join));
            var kinds = reached.IsSuccess ? reached.Value.Stops.Select(p =>
            {
                var at = index.Value.Blocks[p.Block];
                return p.Before == at.Statements.Length ? "Exit" : at.Statements[p.Before] switch
                {
                    Call call when bindings.TryGetValue(call.Identity, out var binding) && binding.Method.Method.Name == ".ctor" => "Constructor",
                    Call call when c.Get(calls, call.Identity) is { IsSuccess: true, Value.Operation.Il.Name: "Throw" } => "Throw",
                    Call => "Call", MemoryRead => "Read", MemoryWrite => "Store", _ => "Statement",
                };
            }).Distinct().ToArray() : [];
            return No("Class." + (kinds is [var kind] ? kind : "Mixed"), "未构造对象的合流含不同的精确类；该使用需要路径拆分。", reached.Why);
        }
        if (block.Handler is not null) return No("ExceptionRegion", "处理入口上的新分配合流尚未证明可移动。");
        foreach (var allocation in inputs.DistinctBy(i => i.Result))
        {
            var source = index.Value.Blocks[allocation.Point.Block];
            if (source.Statements[allocation.Point.Before] is not Call { Unwind: null, DoesNotReturn: false })
                return No("ExceptionRegion", "源分配带异常边或不返回结局，不能移动到汇合处。");
            var barriers = new Dictionary<Point, Reason>();
            var target = new HashSet<Term> { allocation.Result };
            var frontier = new EventFrontierQuery((context, point) =>
            {
                if (point == join) return Outcome<bool>.Success(true);
                var used = Uses(point, target);
                if (!used.IsSuccess) return used;
                if (used.Value) { barriers[point] = new("lowering.Allocation.Merge.Used", "新分配的对象在汇合前已被使用。"); return Outcome<bool>.Success(true); }
                var at = index.Value.Blocks[point.Block];
                if (point.Before == at.Statements.Length) return Outcome<bool>.Success(false);
                var movable = Movable(context, at.Statements[point.Before]);
                if (!movable.IsSuccess || !movable.Value)
                { barriers[point] = new("lowering.Allocation.Merge.Event", "分配与汇合之间有其他事件或不能移动的访问。", movable.Why); return Outcome<bool>.Success(true); }
                return Outcome<bool>.Success(false);
            });
            var reached = c.Get(frontier, new(new(allocation.Point.Block, allocation.Point.Before + 1)));
            if (!reached.IsSuccess) return No("Proof", "分配到汇合的前沿查询失败。", reached.Why);
            if (barriers.Values.FirstOrDefault() is { } reason) return Outcome<AllocationConstructorAnswer>.Success(new(null, null, reason));
            if (reached.Value.HasCycle || reached.Value.ReachesExit || !reached.Value.Stops.SetEquals([join]))
                return No("Flow", "新分配到汇合之间存在循环、退出或未到达汇合的路径。");
        }
        // 原输入与其他合流可能是同一对象的别名，构造之前都不能被使用。
        var aliases = sourceValues.Value.Aliases;
        var first = new EventFrontierQuery((context, point) =>
        {
            var used = Uses(point, aliases); if (!used.IsSuccess || used.Value) return used;
            var at = index.Value.Blocks[point.Block];
            if (point.Before == at.Statements.Length) return Outcome<bool>.Success(false);
            var movable = Movable(context, at.Statements[point.Before]);
            return movable.IsSuccess ? Outcome<bool>.Success(!movable.Value) : movable;
        });
        var firstUse = c.Get(first, new(join));
        if (!firstUse.IsSuccess) return No("Proof", "合流对象的首次使用查询失败。", firstUse.Why);
        if (firstUse.Value.HasCycle || firstUse.Value.ReachesExit || firstUse.Value.Stops is not { Count: 1 })
            return No("FirstUse", "不能证明合流对象首先到达唯一的同类构造调用。");
        var firstPoint = firstUse.Value.Stops.Single(); var stopped = index.Value.Blocks[firstPoint.Block];
        var request = inputs[0] with { Result = merge.Result };
        if (firstPoint.Before < stopped.Statements.Length && stopped.Statements[firstPoint.Before] is Call constructorCall
            && direct.Direct(c, firstPoint, constructorCall, request) is { } constructor)
        {
            if (constructorCall.Unwind is not null) return No("ExceptionRegion", "合流后的构造调用带异常边，尚未证明分配可移动。");
            return Outcome<AllocationConstructorAnswer>.Success(new(constructor, constructorCall.Identity, null)
            { MergedResult = merge.Result, MergedInputs = inputs.Select(i => i.Result).ToImmutableArray(), MergedAliases = EquivalentMerges(c, aliases).ToImmutableArray() });
        }
        var objectUse = Uses(firstPoint, aliases);
        return No(objectUse.IsSuccess && objectUse.Value ? "FirstUse" : "Event", "合流之后首先遇到的使用或事件不是对该对象的同类构造调用。", objectUse.Why);
    }

    // 同一对象可因寄存器传送产生多份合流；复用逐入边同值查询，不能在构造前的入边复制尚未构造的局部。
    private ImmutableHashSet<Term> EquivalentMerges(QueryContext c, ImmutableHashSet<Term> aliases)
    {
        var result = aliases.ToBuilder();
        foreach (var block in c.Snapshot.Blocks)
        {
            var nodes = block.Merges.Where(m => aliases.Contains(m.Result)).ToArray();
            if (nodes.Length == 0) continue;
            var canonical = nodes.Select(m => c.Get(existing, new(block.Identity, m.Inputs)))
                .Where(r => r.IsSuccess).Select(r => r.Value).ToHashSet();
            foreach (var merge in block.Merges.Where(m => m.Result.Width == c.Snapshot.AddressWidth))
            {
                var same = c.Get(existing, new(block.Identity, merge.Inputs));
                if (same.IsSuccess && canonical.Contains(same.Value)) result.Add(merge.Result);
            }
        }
        return result.ToImmutable();
    }

    private Outcome<bool> Movable(QueryContext c, Statement statement)
    {
        var (address, width) = statement switch
        { MemoryRead read => (read.Address, read.Width), MemoryWrite write => (write.Address, write.Width), _ => (null, 0) };
        if (address is null) return Outcome<bool>.Success(false);
        var resolved = c.Get(state.Resolve, address); if (!resolved.IsSuccess) return resolved.Propagate<bool>();
        var location = c.Get(state.Locations, new(resolved.Value, width)); if (!location.IsSuccess) return location.Propagate<bool>();
        if (location.Value.Region == Region.Frame)
        {
            var escaped = c.Get(state.Escapes, 0);
            return escaped.IsSuccess ? Outcome<bool>.Success(!escaped.Value.MayReach(location.Value)) : escaped.Propagate<bool>();
        }
        if (location.Value.Region != Region.Image || statement is not MemoryRead readEntity || names is null) return Outcome<bool>.Success(false);
        var named = c.Get(names, readEntity.Result);
        return named.IsSuccess ? Outcome<bool>.Success(named.Value.Name is EntityName) : named.Propagate<bool>();
    }
}
