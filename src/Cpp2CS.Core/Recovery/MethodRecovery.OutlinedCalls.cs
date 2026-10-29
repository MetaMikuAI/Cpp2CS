using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private readonly Dictionary<ulong, (MachineFunction Function, IdiomResult Idioms)?> outlinedCalls = new();

    private (MachineFunction Function, IdiomResult Idioms)? OutlinedCall(ulong address)
    {
        if (outlinedCalls.TryGetValue(address, out var cached)) return cached;
        (MachineFunction, IdiomResult)? result = null;
        if (facts.Helpers.At(address)?.Kind == HelperKind.Unknown && facts.Code.At(address) is { } range
            && range.Start == address && range.Size <= 1024 && range.ExceptionRegions.Length == 0
            && lifter.Lift(address) is { Succeeded: true } lifted)
        {
            var idioms = rewriter.Run(lifted.Function);
            if (idioms.Errors.Count == 0 && idioms.Residuals.All(r => r.Category.StartsWith("slot-read-without-init:")))
                result = (lifted.Function, idioms);
        }
        return outlinedCalls[address] = result;
    }

    private sealed partial class Context
    {
        private void NormalizeOutlinedCalls(IdiomResult callerIdioms)
        {
            var changed = false;
            foreach (var block in function.Blocks.ToArray())
            {
                if (block.Statements.LastOrDefault() is not Call { Op: null, Kind: CallKind.Direct, Target: Const target } call
                    || !call.Arguments.Any(a => a is FrameAddress)
                    || owner.OutlinedCall(target.Value) is not { } helper
                    || helper.Idioms.ReadSlots.Except(helper.Idioms.InitializedSlots).Except(callerIdioms.InitializedSlots).Any()
                    || !OutlinedCallInlining.Run(function, block, call, helper.Function)) continue;
                cleanupSites.Add(call.Address);
                changed = true;
            }
            if (!changed) return;
            // 展开后先消去捕获帧中的固定指针，再提升不再逃逸的标量。
            Ssa.Propagate.Run(function, Ssa.Dominators.Compute(function));
            PromotePrivateFrameSlots();
            Ssa.Propagate.Run(function, Ssa.Dominators.Compute(function));
            ManagedFramePromotion.Run(facts, function, owner.abi, owner.lifter.Calls, owner.lifter.Machine.Convention.StackPointer,
                owner.abi.Classify(method, out _)?.Return);
            function.Problems.AddRange(Ssa.SsaCheck.Verify(function, Ssa.Dominators.Compute(function)));
        }
    }
}
