
namespace Cpp2CS.Recovery;

internal static class RecoveryPipeline
{
    internal static MethodRecoveryResult Run(this RecoveryScope ctx)
    {
        ManagedBody? partial = null;
        if (ctx.Prepare())
        {
            if (ctx.Analyze() is { } analysisFailure)
                ctx.Record(analysisFailure, ctx.entry);
            else if (!ctx.Build().TryGet(out var built, out var buildFailure))
                ctx.Record(buildFailure, ctx.entry);
            else
            {
                var body = DeadCopiesRules.DropUnusedRegisterCopies(ctx.RewriteAwaiters(built));
                bool Leftover(ManagedStatement s) => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)).Any(RecoveryDiagnostics.FragmentInside);
                partial = body with
                {
                    Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(s => Leftover(s) ? new ManagedHole(s.Address, "结构体 片未拆回叶子", s is ManagedJump or ManagedBranch or ManagedSwitch or ManagedReturn or ManagedCall { Tail: true }) : s).ToArray() }).ToArray()
                };
                if (body.Blocks.SelectMany(b => b.Statements).FirstOrDefault(Leftover) is { } leftover)
                    ctx.Record(RecoveryDiagnostics.Fail(leftover.Address, "结构体 片未拆回叶子", rule: "Run"), ctx.entry);
                else
                    foreach (var proof in RuleRegistry.Proofs)
                        proof(ctx, body);
                if (ctx.ledger.Count == 0)
                    return new(ctx.method, ctx.entry, ctx.owner.RestoreBaseConstructor(body), ctx.ledger.Holes)
                    {
                        Passes = ctx.passSteps.ToArray(),
                        Analyses = ctx.analysisSteps.ToArray(),
                        Calls = ctx.State.Calls.callBindings.Resolutions.ToArray(),
                        Rules = ctx.ruleTraces.ToArray()
                    };
                ctx.ledger.Finish();
            }
        }

        return new(ctx.method, ctx.entry, null, ctx.ledger.Holes)
        {
            Partial = partial is null ? null : RecoveryPipeline.Summarized(partial, ctx.ledger.Holes),
            Passes = ctx.passSteps.ToArray(),
            Analyses = ctx.analysisSteps.ToArray(),
            Calls = ctx.State.Calls.callBindings.Resolutions.ToArray(),
            Rules = ctx.ruleTraces.ToArray()
        };
    }

    /// <summary>没有落在某条语句上的洞（异常区域、签名等方法级的洞）汇总成方法入口处的一条标记。</summary>
    internal static ManagedBody Summarized(ManagedBody partial, IReadOnlyList<RecoveryHole> holes)
    {
        var marked = partial.Blocks.SelectMany(b => b.Statements).OfType<ManagedHole>().Select(h => h.Reason).ToHashSet();
        var unmarked = holes.Where(h => !h.Derived && !marked.Contains(h.Reason)).Select(h => $"0x{h.Address:x} {h.Reason}").Distinct().ToArray();
        if (unmarked.Length == 0 || partial.Blocks.Count == 0)
            return partial;
        var first = partial.Blocks[0];
        var summary = new ManagedHole(0, "未恢复：" + string.Join("；", unmarked.Take(4)) + (unmarked.Length > 4 ? $"；等 {unmarked.Length} 处" : ""), false);
        return partial with
        {
            Blocks = partial.Blocks.Skip(1).Prepend(first with { Statements = first.Statements.Prepend(summary).ToArray() }).ToArray()
        };
    }
}
