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
        foreach (var step in RuleRegistry.Analyses)
        {
            ctx.currentStep = step.Id;
            ctx.Rewriter.Attach(ctx.function);
            var version = ctx.analyses.Version;
            var inputTypes = ctx.State.Types.known.Count;
            var started = System.Diagnostics.Stopwatch.GetTimestamp();
            var mutable = step.Kind == StepKind.Rewrite;
            var before = mutable ? null : new MethodSnapshot(0, ctx.blocks, new Dictionary<Variable, Phi>());
            if (step.Refresh.HasFlag(StepRefresh.Types))
                ctx.Maintain.Types($"{step.Id}.entry");
            var failure = step.Run(ctx);
            ctx.Rewriter.Attach(ctx.function);
            if (before is not null && !before.Matches(ctx.blocks, new Dictionary<Variable, Phi>()))
                throw new InvalidOperationException($"只读分析改写了机器 IR：{step.Id}");
            if (ctx.analyses.Refresh(ctx.blocks, ctx.State.Exceptions.exceptionPhis))
                ctx.definitions = ctx.analyses.Get(Definitions.Analysis);
            ctx.trace.Add(new(TraceKind.Step, step.Id, step.Id)
            {
                StepKind = mutable ? "machine-pass" : "analysis",
                Invalidates = mutable ? step.Invalidates.ToString() : null,
                InputVersion = version,
                OutputVersion = ctx.analyses.Version,
                InputTypes = inputTypes,
                OutputTypes = ctx.State.Types.known.Count,
                Milliseconds = System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds,
            });
            if (failure is not null)
                return failure;
        }

        return null;
    }
}
