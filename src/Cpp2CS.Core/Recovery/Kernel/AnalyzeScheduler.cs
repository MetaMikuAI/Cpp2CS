using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>Analyze 的调度器：按注册表的顺序运行步骤，在步骤边界挂接改写器、执行声明的维护、只读检查与定义刷新，并记录追踪。</summary>
internal static class AnalyzeScheduler
{
    internal static RecoveryFailure? Analyze(this MethodSession ctx)
    {
        ctx.currentStep = "analyze";
        ctx.Maintain.Definitions("kernel.analyze.entry");
        // 依赖边取改写前的数据流：帧改写把别名换成 TypedFrame，但值仍然来自原来的来源。
        foreach (var (source, target) in ctx.definitions.DataFlow)
            ctx.ledger.Dependency(source, target);
        ctx.ledger.PropagateExisting();
        // 异常 φ 表在 Prepare 中建好，分析阶段只读（只读检查比对它）
        var exceptionPhis = ctx.State.Exceptions.exceptionPhis;
        foreach (var step in RuleRegistry.Analyses)
        {
            ctx.currentStep = step.Id;
            ctx.Rewriter.Attach(ctx.function);
            var version = ctx.analyses.Version;
            var inputTypes = ctx.State.Types.known.Count;
            var started = System.Diagnostics.Stopwatch.GetTimestamp();
            var mutable = step.Kind == StepKind.Rewrite;
            // 只读检查：全部块（不只块视图）与异常 φ；分析步骤期间关闭写许可，禁止重置块视图、刷新定义与 IR 编辑
            var before = mutable ? null : new MethodSnapshot(0, ctx.function.Blocks, exceptionPhis);
            if (step.Refresh.HasFlag(StepRefresh.Types))
                ctx.Maintain.Types($"{step.Id}.entry");
            if (!mutable)
                (ctx.Rewriter.Closed, ctx.Maintain.ReadOnly) = (step.Id, step.Id);
            var failure = step.Run(ctx);
            (ctx.Rewriter.Closed, ctx.Maintain.ReadOnly) = (null, null);
            ctx.Rewriter.Attach(ctx.function);
            if (before is not null && !before.Matches(ctx.function.Blocks, exceptionPhis))
                throw new InvalidOperationException($"只读分析改写了机器 IR：{step.Id}");
            if (ctx.analyses.Refresh(ctx.blocks, exceptionPhis))
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
