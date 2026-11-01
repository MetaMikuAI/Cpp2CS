using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class RecoveryAnalysis
{
    internal static RecoveryFailure? Analyze(this RecoveryScope ctx)
    {
        ctx.currentStep = "analyze";
        ctx.Maintain.Definitions("kernel.analyze.entry");
        // 依赖边取改写前的数据流：帧改写把别名换成 TypedFrame，但值仍然来自原来的来源。
        foreach (var (source, target) in ctx.definitions.DataFlow)
            ctx.ledger.Dependency(source, target);
        ctx.ledger.PropagateExisting();
        foreach (var (name, run) in RuleRegistry.Analyses)
        {
            ctx.currentStep = name;
            ctx.Rewriter.Attach(ctx.function);
            var version = ctx.analyses.Version;
            var inputTypes = ctx.State.Types.known.Count;
            var started = System.Diagnostics.Stopwatch.GetTimestamp();
            var mutable = RuleRegistry.MachinePasses.TryGetValue(name, out var invalidates);
            var before = mutable ? null : new MethodSnapshot(0, ctx.blocks, new Dictionary<Variable, Phi>());
            var failure = run(ctx);
            ctx.Rewriter.Attach(ctx.function);
            if (before is not null && !before.Matches(ctx.blocks, new Dictionary<Variable, Phi>()))
                throw new InvalidOperationException($"只读分析改写了机器 IR：{name}");
            if (ctx.analyses.Refresh(ctx.blocks, ctx.State.Exceptions.exceptionPhis))
                ctx.definitions = ctx.analyses.Get(Definitions.Analysis);
            ctx.analysisSteps.Add(new(name, version, ctx.analyses.Version, inputTypes, ctx.State.Types.known.Count, System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds)
            { Kind = mutable ? "machine-pass" : "analysis", Invalidates = mutable ? invalidates.ToString() : null });
            if (failure is not null)
                return failure;
        }

        return null;
    }
}
