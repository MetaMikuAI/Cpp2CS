using Cpp2CS.Ir;
using Cpp2CS.Idioms;
using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

internal static class OutlinedCallsRules
{
    internal static void NormalizeOutlinedCalls(this RecoveryScope ctx, IdiomResult callerIdioms)
    {
        var changed = false;
        foreach (var call in ctx.function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
            .Where(c => c is { Op: null, Kind: CallKind.Direct, Target: Const }).ToArray())
        {
            var target = (Const)call.Target;
            if (ctx.facts.Helpers.At(target.Value)?.Kind != HelperKind.Unknown) continue;
            var block = ctx.function.Blocks.Single(b => b.Statements.Contains(call));
            var used = ctx.function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands)
                .SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)
                .Concat(ctx.function.Blocks.SelectMany(b => b.Statements).OfType<Phi>().SelectMany(p => p.Sources)).ToHashSet();
            var results = call.Defines.Where(v => v is not null && used.Contains(v)).ToArray();
            if (results.Length > 1 || results.Length == 1 && results[0].Storage != Storage.Gpr(0)) continue;
            var returned = results.Length == 1 ? new Read(Storage.Gpr(0), 64) : null;
            if (ctx.owner.NativeMethods.OutlinedCall(target.Value, returned) is not { } helper || helper.Idioms.ReadSlots.Except(helper.Idioms.InitializedSlots).Except(callerIdioms.InitializedSlots).Any() || !OutlinedCallInlining.Run(ctx.function, block, call, helper.Function))
                continue;
            ctx.State.Calls.cleanupSites.Add(call.Address);
            changed = true;
        }

        if (!changed)
            return;
        // 展开后先消去捕获帧中的固定指针，再提升不再逃逸的标量。
        Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
        // 辅助函数的 MethodInfo 实参在展开后才成为常量；沿用已有 RGCTX 与静态字段规则。
        var symbols = new IdiomState(ctx.owner.rewriter, ctx.function);
        symbols.Symbols(rgctx: true);
        symbols.defs = new IdiomRewriter.Defs(ctx.function);
        symbols.RefreshOperands();
        foreach (var (template, count) in symbols.Result.Hits)
            callerIdioms.Hits[template] = callerIdioms.Hits.GetValueOrDefault(template) + count;
        callerIdioms.ReadSlots.UnionWith(symbols.Result.ReadSlots);
        ctx.PromotePrivateFrameSlots();
        Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
        ManagedFramePromotion.Run(ctx.facts, ctx.function, ctx.owner.abi, ctx.owner.lifter.Calls, ctx.owner.lifter.Machine.Convention.StackPointer, ctx.owner.abi.Classify(ctx.method, out _)?.Return);
        ctx.function.Problems.AddRange(Cpp2CS.Machine.Ssa.SsaCheck.Verify(ctx.function, ctx.Dominators));
    }
}
