using Cpp2CS.Ir;
using Cpp2CS.Idioms;

namespace Cpp2CS.Recovery;

internal static class OutlinedCallsRules
{
    internal static void NormalizeOutlinedCalls(this RecoveryScope ctx, IdiomResult callerIdioms)
    {
        var changed = false;
        foreach (var block in ctx.function.Blocks.ToArray())
        {
            if (block.Statements.LastOrDefault() is not Call { Op: null, Kind: CallKind.Direct, Target: Const target } call || !call.Arguments.Any(a => a is FrameAddress) || ctx.owner.NativeMethods.OutlinedCall(target.Value) is not { } helper || helper.Idioms.ReadSlots.Except(helper.Idioms.InitializedSlots).Except(callerIdioms.InitializedSlots).Any() || !OutlinedCallInlining.Run(ctx.function, block, call, helper.Function))
                continue;
            ctx.State.Calls.cleanupSites.Add(call.Address);
            changed = true;
        }

        if (!changed)
            return;
        // 展开后先消去捕获帧中的固定指针，再提升不再逃逸的标量。
        Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
        ctx.PromotePrivateFrameSlots();
        Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
        ManagedFramePromotion.Run(ctx.facts, ctx.function, ctx.owner.abi, ctx.owner.lifter.Calls, ctx.owner.lifter.Machine.Convention.StackPointer, ctx.owner.abi.Classify(ctx.method, out _)?.Return);
        ctx.function.Problems.AddRange(Cpp2CS.Machine.Ssa.SsaCheck.Verify(ctx.function, ctx.Dominators));
    }
}
