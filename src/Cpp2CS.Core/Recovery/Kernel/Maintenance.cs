using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>
/// 维护动作的内核接口：规则经它请求类型推断、重建定义、重置块视图与重跑已注册的分析。
/// 每个请求立即执行，时机与次数和原来的直接调用相同，并记入方法的维护记录；记录只读取当前版本，不为记录而刷新。
/// </summary>
internal sealed class Maintenance(RecoveryScope ctx)
{
    /// <summary>类型推断。</summary>
    public void Types(string reason) => Record("types", reason, ctx.InferTypes);

    /// <summary>重建定义索引：一次快照刷新，快照变化时定义版本递增（调用解析缓存以这个版本为键）。</summary>
    public void Definitions(string reason) => Record("definitions", reason, () => ctx.definitions = ctx.IndexDefinitions());

    /// <summary>
    /// 重置块视图。传入 <c>function.Blocks</c> 时记下的是这个列表对象本身：之后原地增加的块立即可见，
    /// 列表被整体替换后视图仍指向旧列表，直到下一次重置；传入数组时是快照。
    /// </summary>
    public void Blocks(IReadOnlyList<Block> blocks, string reason) => Record("blocks", reason, () => ctx.blocks = blocks);

    /// <summary>重跑一个已注册的分析：直接调用，不挂接改写器、不做只读快照、不刷新定义、不追加分析步骤记录。</summary>
    public void Rerun(Action<RecoveryScope> step, string reason) => Record("rerun", reason, () => step(ctx));

    /// <summary>重新计算支配树（每次都重算，不经缓存）。</summary>
    public Dominators Dominators(string reason)
    {
        Dominators? result = null;
        Record("dominators", reason, () => result = Cpp2CS.Machine.Ssa.Dominators.Compute(ctx.function));
        return result!;
    }

    /// <summary>
    /// 不动点组：反复执行 <paramref name="round"/>，返回 false（本轮无改动）即收敛。达到预算时与原来的有界循环一样静默结束，
    /// 记为 BudgetExhausted；原来没有预算的循环取远大于正常轮数的上限，耗尽时由调用方留洞。返回是否收敛。
    /// </summary>
    public bool Fixpoint(string id, int budget, Func<bool> round)
    {
        var version = ctx.analyses.Version;
        var rounds = 0;
        var stable = false;
        while (rounds < budget)
        {
            rounds++;
            if (!round()) { stable = true; break; }
        }
        ctx.maintenanceSteps.Add(new(ctx.currentStep, "fixpoint", id, version, ctx.analyses.Version, rounds, stable ? "Stable" : "BudgetExhausted"));
        return stable;
    }

    /// <summary>原来没有预算的改写循环所用的安全上限。</summary>
    public const int SafetyBudget = 1000;

    internal void Record(string action, string reason, Action run)
    {
        var version = ctx.analyses.Version;
        run();
        ctx.maintenanceSteps.Add(new(ctx.currentStep, action, reason, version, ctx.analyses.Version));
    }
}

/// <summary>IR 级维护动作的内核接口：传播、删除死定义、清理、控制流化简与带异常片段维护的删除。立即执行并记录。</summary>
internal sealed class Editing(RecoveryScope ctx, Maintenance maintain)
{
    public void Propagate(Dominators dominators, string reason) =>
        maintain.Record("propagate", reason, () => Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, dominators));

    public void RemoveDead(string reason) => maintain.Record("remove-dead", reason, () => Cpp2CS.Machine.Ssa.Propagate.RemoveDead(ctx.function));

    /// <summary>清理并把清理发现的问题追加到函数的问题列表。</summary>
    public void Cleanup(string reason) => maintain.Record("cleanup", reason, () => ctx.function.Problems.AddRange(Lowering.Cleanup(ctx.function)));

    public bool Simplify(string reason)
    {
        var changed = false;
        maintain.Record("simplify", reason, () => changed = ControlFlow.Simplify(ctx.function));
        return changed;
    }

    /// <summary>删除死定义；异常布局已排好时按保留下来的语句重算各异常片段的起止位置。</summary>
    public void RemoveDeadDefinitions(string reason) => maintain.Record("remove-dead-definitions", reason, () =>
    {
        var fragments = ctx.ArrangedFragments();
        var previous = fragments?.Select(f => f.Block).Distinct().ToDictionary(b => b, b => b.Statements.ToArray());
        Cpp2CS.Machine.Ssa.Propagate.RemoveDead(ctx.function);
        if (previous is null)
            return;
        foreach (var group in fragments!.GroupBy(f => f.Block))
        {
            var retained = group.Key.Statements.ToHashSet(ReferenceEqualityComparer.Instance);
            var old = previous[group.Key];
            var positions = new int[old.Length + 1];
            for (var i = 0; i < old.Length; i++)
                positions[i + 1] = positions[i] + (retained.Contains(old[i]) ? 1 : 0);
            foreach (var fragment in group)
            {
                fragment.First = positions[fragment.First];
                fragment.Limit = positions[fragment.Limit];
            }
        }
    });
}
