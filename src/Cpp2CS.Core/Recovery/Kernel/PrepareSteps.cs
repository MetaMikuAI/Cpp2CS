using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Idioms;
using Cpp2CS.Machine.Storage;

namespace Cpp2CS.Recovery;

/// <summary>
/// 内核的 Prepare 步骤：包装机器层与 L2 的算法、L2 结果的消费与方法级的收尾。
/// Machine 与 Idioms 不能引用 Recovery，这些步骤因此注册在 Kernel。
/// </summary>
internal static class PrepareSteps
{
    /// <summary>提升，并把机器函数与提升所用的机器模型交给后续步骤；失败时记洞并中止。</summary>
    [Step("kernel.lift", StepPhase.Prepare, StepKind.Rewrite)]
    internal static PrepareOutcome Lift(RecoveryScope scope, PreparedMethod prepared)
    {
        var lifted = scope.owner.lifter.Lift(scope.entry, prepared.ReturnValue);
        if (!lifted.Succeeded)
        {
            scope.Hole(scope.entry, $"提升 {lifted.Errors[0]}", rule: "Prepare");
            return PrepareOutcome.Stop;
        }

        scope.function = lifted.Function;
        prepared.Abi = scope.owner.abi;
        prepared.Calls = scope.owner.lifter.Calls;
        prepared.StackPointer = scope.owner.lifter.Machine.Convention.StackPointer;
        return PrepareOutcome.Continue;
    }

    /// <summary>L2；它的步骤记在本步骤之前。</summary>
    [Step("kernel.idioms", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void RunIdioms(RecoveryScope scope, PreparedMethod prepared)
    {
        prepared.Idioms = scope.owner.rewriter.Run(scope.function);
        scope.passSteps.AddRange(prepared.Idioms.Passes);
    }

    /// <summary>私有帧槽提升（泛型实参含按值布局的聚合时）。</summary>
    [Step("kernel.promote-private-frame-slots", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void PromotePrivateFrameSlots(RecoveryScope scope) => scope.PromotePrivateFrameSlots();

    /// <summary>L2 的错误转洞；有错误时中止。</summary>
    [Step("kernel.idiom-errors", StepPhase.Prepare, StepKind.Analysis)]
    internal static PrepareOutcome IdiomErrors(RecoveryScope scope, PreparedMethod prepared)
    {
        foreach (var error in prepared.Idioms.Errors)
            scope.Hole(scope.entry, $"L2 {error}", rule: "Prepare");
        return prepared.Idioms.Errors.Count > 0 ? PrepareOutcome.Stop : PrepareOutcome.Continue;
    }

    [Step("kernel.remove-dead", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void RemoveDead(RecoveryScope scope) => scope.Edit.RemoveDead("kernel.remove-dead");

    /// <summary>原值写回删除。</summary>
    [Step("kernel.frame-writebacks", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void RemoveFrameWritebacks(RecoveryScope scope) => FrameWritebacks.Run(scope.function);

    /// <summary>帧常量下标；记下是否有改写，供传播步骤判断。</summary>
    [Step("kernel.frame-constant-indices", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void IndexConstantFrames(RecoveryScope scope, PreparedMethod prepared) => prepared.ConstantFrameIndices = FrameIndexAnalysis.Run(scope.function) > 0;

    /// <summary>有常量下标时：传播，再提升私有帧槽。</summary>
    [Step("kernel.propagate-constant-indices", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void PropagateConstantIndices(RecoveryScope scope)
    {
        scope.Edit.Propagate(scope.Dominators, "kernel.propagate-constant-indices");
        scope.PromotePrivateFrameSlots();
    }

    /// <summary>委托调用归一；有改写时清理，并删除对应的间接调用残余。</summary>
    [Step("kernel.delegate-calls", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void NormalizeDelegateCalls(RecoveryScope scope, PreparedMethod prepared)
    {
        if (!DelegateCallNormalizer.Run(scope.facts, scope.function, prepared.Idioms))
            return;
        scope.Edit.Cleanup("kernel.delegate-calls");
        var delegates = scope.function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c is { Op.Kind: OpKind.CallDelegate, Target: Symbol { Kind: SymbolKind.Method }, DelegateReceiver: not null }).Select(c => c.Address).ToHashSet();
        prepared.Idioms.Residuals.RemoveAll(r => r.Category.StartsWith("indirect:", StringComparison.Ordinal) && delegates.Contains(r.Address));
    }

    /// <summary>L2 残余转洞；压制清理 thunk 与共享泛型站点，死的类元数据读取只记规则追踪。</summary>
    [Step("kernel.residual-holes", StepPhase.Prepare, StepKind.Analysis)]
    internal static void ResidualHoles(RecoveryScope scope, PreparedMethod prepared)
    {
        foreach (var residual in prepared.Idioms.Residuals)
        {
            // 写屏障实参裁剪后，部分 Class 读取已被 SSA 证明无使用；旧 L2 诊断不再对应活语句。
            if (residual.Category.StartsWith("load:Class+", StringComparison.Ordinal) && scope.function.Dead.Any(p => p.Define.Address == residual.Address && ExprMap.Walk(p.Define.Value).OfType<Load>().Any(l => ExprMap.Walk(l.Address).Any(e => e is Symbol { Kind: SymbolKind.Class }))) && !scope.function.Blocks.SelectMany(b => b.Statements).Any(s => s.Address == residual.Address))
            {
                scope.ruleTraces.Add(new("runtime.dead-class-read", residual.Address, RewriteStatus.Applied, "runtime.unused-class-metadata", "Class 读取的全部使用已由 SSA 消除，保留原诊断与死定义证据", new("ssa.dead-definition", [residual.Address], [residual.Category, residual.Detail])));
                continue;
            }

            // 没有身份证据的未注册调用交给 L3 的调用解析（方法的本地副本，CopyOf）；解析不了时在调用处留洞。
            if (residual.Category is not ("helper:WriteBarrier" or "call:unregistered-managed") && !scope.State.Calls.cleanupSites.Contains(residual.Address) && !scope.State.Calls.sharedSites.Contains(residual.Address))
            {
                var hole = scope.Hole(residual.Address, $"残余 {residual.Category}", rule: "Prepare");
                foreach (var statement in scope.function.Blocks.SelectMany(b => b.Statements).Where(s => s.Address == residual.Address))
                    scope.ledger.Block(statement, hole);
            }
        }
    }

    /// <summary>块视图重置为全部块。</summary>
    [Step("kernel.blocks", StepPhase.Prepare, StepKind.Analysis)]
    internal static void ResetBlocks(RecoveryScope scope) => scope.Maintain.Blocks(scope.function.Blocks, "kernel.blocks");

    /// <summary>控制流问题转洞。</summary>
    [Step("kernel.problem-holes", StepPhase.Prepare, StepKind.Analysis)]
    internal static void ProblemHoles(RecoveryScope scope)
    {
        foreach (var problem in scope.function.Problems)
            scope.Hole(scope.entry, $"控制流 {problem}", rule: "Prepare");
    }
}
