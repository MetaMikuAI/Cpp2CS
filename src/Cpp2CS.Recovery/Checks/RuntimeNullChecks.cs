using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Checks;

/// <summary>直接运行时判空与分支形检查共用访问前沿；失败时由下降保留条件抛出。</summary>
public sealed class RuntimeNullCheckQuery(CheckQueries q) : Query<CallIdentity, CheckAbsorption>
{
    public override Outcome<CheckAbsorption> Compute(QueryContext c, CallIdentity key)
    {
        Outcome<CheckAbsorption> No(string code, string text) => Outcome<CheckAbsorption>.Success(new(false, [], new("check.null." + code, text)));
        var classified = c.Get(q.Calls, key); if (!classified.IsSuccess) return classified.Propagate<CheckAbsorption>();
        if (classified.Value.Operation?.Il.Name != "NullCheck" || classified.Value.Inputs?.GetValueOrDefault("value")?.Source is not TermSource input)
            return No("binding", "判空调用没有完整绑定的输入。");
        var block = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == key));
        int index = 0;
        while (block.Statements[index] is not Call found || found.Identity != key) index++;
        if (((Call)block.Statements[index]).Unwind is not null) return No("unwind", "判空带异常出口，保持原抛出位置。");
        var frontier = c.Get(q.AccessFrontier, new(new(block.Identity, index + 1)));
        if (!frontier.IsSuccess) return frontier.Propagate<CheckAbsorption>();
        if (frontier.Value.HasCycle) return No("cycle", "匹配访问前可能进入循环。");
        if (frontier.Value.ReachesExit || frontier.Value.Stops.Count == 0) return No("exit", "有路径在匹配访问前退出。");
        foreach (var point in frontier.Value.Stops)
        {
            var info = c.Get(q.Points, point); if (!info.IsSuccess) return info.Propagate<CheckAbsorption>();
            var matched = q.NullAccess(c, info.Value, input.Term); if (!matched.IsSuccess) return matched.Propagate<CheckAbsorption>();
            if (!matched.Value) return No("frontier", "前沿先遇到其他事件、写入或不同对象的访问。");
        }
        return Outcome<CheckAbsorption>.Success(new(true, frontier.Value.Stops));
    }
}

/// <summary>被直接判空吸收的非虚实例调用必须输出 callvirt；计划与调用下降次序无关。</summary>
public sealed class NullCheckedCallsQuery(CheckQueries q) : Query<int, ImmutableHashSet<CallIdentity>>
{
    public override Outcome<ImmutableHashSet<CallIdentity>> Compute(QueryContext c, int key)
    {
        var result = ImmutableHashSet.CreateBuilder<CallIdentity>();
        foreach (var call in c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (c.Get(q.Calls, call.Identity) is not { IsSuccess: true, Value.Operation.Il.Name: "NullCheck" }) continue;
            var check = c.Get(q.NullChecks, call.Identity); if (!check.IsSuccess) return check.Propagate<ImmutableHashSet<CallIdentity>>();
            if (!check.Value.CanAbsorb) continue;
            foreach (var point in check.Value.Accesses)
                if (c.Get(q.Points, point) is { IsSuccess: true, Value.ReceiverRequiresCallvirt: true }
                    && CheckQueries.Statement(c, point) is Call target) result.Add(target.Identity);
        }
        return Outcome<ImmutableHashSet<CallIdentity>>.Success(result.ToImmutable());
    }
}
