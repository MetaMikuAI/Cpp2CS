using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery;

internal static class TypingRules
{
    internal static void InferTypes(this RecoveryScope ctx)
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

    internal static void Sync(this RecoveryScope ctx, Dictionary<Variable, TypeResult> solution, bool final = false)
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

}
