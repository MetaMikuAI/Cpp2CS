using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>
/// 维护动作的内核接口：规则经它请求类型推断、重建定义、重置块视图与重跑已注册的分析。
/// 每个请求立即执行，时机与次数和原来的直接调用相同，并记入方法的维护记录；记录只读取当前版本，不为记录而刷新。
/// </summary>
internal sealed class Maintenance(MethodSession ctx)
{
    /// <summary>非空时处于只读的分析步骤中（值为步骤 Id）：禁止重置块视图、刷新定义与 IR 编辑。</summary>
    internal string? ReadOnly { get; set; }

    internal void Check(string action) => Allowed(action);

    private void Allowed(string action)
    {
        if (ReadOnly is not null)
            throw new InvalidOperationException($"只读分析步骤 {ReadOnly} 不得执行维护动作 {action}");
    }

    /// <summary>类型推断。</summary>
    public void Types(string reason) => Record("types", reason, ctx.Rewrite.InferTypes);

    /// <summary>重建定义索引：一次快照刷新，快照变化时定义版本递增（调用解析缓存以这个版本为键）。</summary>
    public void Definitions(string reason)
    {
        Allowed("definitions");
        Record("definitions", reason, () => ctx.definitions = ctx.IndexDefinitions());
    }

    /// <summary>把块视图限定在给定的块上（异常布局的正常闭包或保留块）。块视图总是按当前的块列表计算，不需要重置。</summary>
    public void ScopeBlocks(IEnumerable<Block> kept, string reason)
    {
        Allowed("blocks");
        Record("blocks", reason, () => ctx.ScopeBlocks(kept));
    }

    /// <summary>
    /// 按 Id 重跑一个已注册的步骤：直接调用，不挂接改写器、不做只读快照、不刷新定义、不追加分析步骤记录。
    /// 只能重跑不会失败的步骤（方法返回 void），否则失败无处报告。
    /// </summary>
    public void Rerun(string id, string reason)
    {
        var step = RuleRegistry.Step(id);
        if (step.CanFail)
            throw new InvalidOperationException($"重跑的步骤 {id} 可能失败，不能经 Rerun 调用");
        Record($"rerun:{id}", reason, () => step.Run(ctx));
    }

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
        ctx.trace.Add(new(TraceKind.Fixpoint, id, ctx.currentStep)
        {
            InputVersion = version,
            OutputVersion = ctx.analyses.Version,
            Rounds = rounds,
            Convergence = stable ? "Stable" : "BudgetExhausted",
        });
        return stable;
    }

    /// <summary>原来没有预算的改写循环所用的安全上限。</summary>
    public const int SafetyBudget = 1000;

    internal void Record(string action, string reason, Action run)
    {
        if (action is "propagate" or "remove-dead" or "cleanup" or "simplify" or "remove-dead-definitions")
            Allowed(action);
        var version = ctx.analyses.Version;
        run();
        ctx.trace.Add(new(TraceKind.Maintenance, action, ctx.currentStep) { Reason = reason, InputVersion = version, OutputVersion = ctx.analyses.Version });
    }
}

/// <summary>IR 级维护动作的内核接口：传播、删除死定义、清理、控制流化简与带异常片段维护的删除。立即执行并记录。</summary>
internal sealed class Editing(MethodSession ctx, Maintenance maintain)
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

    /// <summary>
    /// 插入一条语句；异常布局已排好时，同块中起止位置在插入点之后的异常片段随之后移。IR 编辑，不记入维护记录。
    /// </summary>
    public void Insert(Block block, int index, Stmt statement)
    {
        maintain.Check("insert");
        if (ctx.Analysis.ArrangedFragments() is { } fragments)
            foreach (var fragment in fragments.Where(f => f.Block == block))
            {
                if (fragment.First > index)
                    fragment.First++;
                if (fragment.Limit > index)
                    fragment.Limit++;
            }

        ctx.Rewriter.Insert(block, index, statement);
    }

    /// <summary>删除死定义；异常布局已排好时按保留下来的语句重算各异常片段的起止位置。</summary>
    public void RemoveDeadDefinitions(string reason) => maintain.Record("remove-dead-definitions", reason, () =>
    {
        var fragments = ctx.Analysis.ArrangedFragments();
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
