using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery;

internal static class TypingRules
{
    internal static void InferTypes(this RewriteScope ctx)
    {
        ctx.State.Types.typingSeeds ??= ctx.State.Types.known.ToDictionary();
        var (view, entryTypes, input) = ctx.TypingInputsFor();
        TypingContext context = null!;
        context = new(view, ctx.types, entryTypes, call =>
        {
            ctx.Sync(context.Solution);
            return ctx.Resolve(call);
        });
        var trace = ctx.facts.Options.Diagnostics.Typing.Contains(ctx.entry) ? new TraceContributor(ctx.facts.Options.Diagnostics, ctx.entry) : null;
        var result = new TypeEngine([.. TypingContributors.Create(input), .. trace is null ? [] : new ITypeContributor[] { trace }]).Run(context);
        ctx.State.Types.syncedSolution = null;
        ctx.Sync(result.Solution, final: true);
        if (!result.Converged)
            ctx.Hole(ctx.entry, $"类型推断 {result.Rounds} 轮后未收敛", rule: "InferTypes");
        trace?.Print(result.Solution, result.Rounds);
    }

    internal static void Sync(this AnalysisScope ctx, Dictionary<Variable, TypeResult> solution, bool final = false)
    {
        if (ReferenceEquals(ctx.State.Types.syncedSolution, solution))
            return;
        ctx.State.Types.syncedSolution = solution;
        ctx.State.Calls.callBindings.InvalidateTypes();
        ctx.State.Types.known.Clear();
        foreach (var (variable, result) in solution)
        {
            if (ctx.State.Runtime.runtime.Contains(variable))
                continue;
            var type = result switch
            {
                ManagedResult managed => managed.Type,
                ConflictResult { Lower: { } lower } when !final => lower,
                _ => null,
            };
            if (type is not null)
                ctx.State.Types.known[variable] = type;
        }

        foreach (var (variable, type) in ctx.State.Types.typingSeeds!)
            ctx.State.Types.known[variable] = type;
    }

    /// <summary>类型推断；认出新的类型检查后（klass 加载成为运行时引用），标记运行时值再推断一次。</summary>
    [Step("typing.infer", StepPhase.Analyze, StepKind.Rewrite, Order = 900, After = ["runtime.mark", "lowering.inline", "frames.slots", "construction.allocations", "control.absorb-checks"], Name = "类型")]
    internal static void Typing(this RewriteScope ctx)
    {
        ctx.Maintain.Types("typing.infer.main");
        if (ctx.PrepareTypeChecks())
        {
            ctx.Maintain.Rerun("runtime.mark", "typing.type-checks");
            ctx.Maintain.Types("typing.infer.type-checks");
        }

        ctx.PrepareUnusedReceiverPhis();
        ctx.TrimIndirectArguments(typed: true);
        ctx.NarrowTypedScalars();
    }
}
