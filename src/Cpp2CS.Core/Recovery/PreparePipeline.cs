using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Idioms;

namespace Cpp2CS.Recovery;

internal static class PreparePipeline
{
    internal static bool Prepare(this RecoveryScope ctx)
    {
        if (!ctx.BindSignature(out var signature, out var returnValue)) return false;
        var lifted = ctx.owner.lifter.Lift(ctx.entry, returnValue);
        if (!lifted.Succeeded)
        {
            ctx.Hole(ctx.entry, $"提升 {lifted.Errors[0]}", rule: "Prepare");
            return false;
        }

        ctx.function = lifted.Function;
        var idioms = ctx.owner.rewriter.Run(ctx.function);
        ctx.passSteps.AddRange(idioms.Passes);
        ctx.Passes.Run("prepare.BindSharedReferences", () =>
        {
            if (ctx.SharedDefinition)
                ctx.BindSharedReferences();
        });
        ctx.Passes.Run("prepare.PromotePrivateFrameSlots", () =>
        {
            if (ctx.method.TypeArguments.Concat(ctx.method.MethodArguments).Any(t => t is GenericParameterRef { NativeAggregate: not null }))
                ctx.PromotePrivateFrameSlots();
        });
        ctx.Passes.Run("prepare.NormalizeSharedFields", () =>
        {
            ctx.NormalizeSharedFields();
        });
        ctx.Passes.Run("prepare.NormalizeSharedValues", () =>
        {
            ctx.NormalizeSharedValues();
        });
        ctx.Passes.Run("prepare.StackCanaryRecognition.Run", () =>
        {
            StackCanaryRecognition.Run(ctx.function, extent: new ManagedCallFrames(ctx.facts, ctx.owner.abi).ArgumentSize);
        });
        ctx.Passes.Run("prepare.NormalizeDelegateChoices", () =>
        {
            ctx.NormalizeDelegateChoices();
        });
        foreach (var error in idioms.Errors)
            ctx.Hole(ctx.entry, $"L2 {error}", rule: "Prepare");
        if (idioms.Errors.Count > 0)
            return false;
        ctx.Passes.Run("prepare.NormalizeScalarVectors", () =>
        {
            ctx.NormalizeScalarVectors();
        });
        ctx.Passes.Run("prepare.VectorPhiProjection.Run", () =>
        {
            VectorPhiProjection.Run(ctx.function.Blocks);
        });
        ctx.Passes.Run("prepare.CallArgumentProjection.Run", () =>
        {
            CallArgumentProjection.Run(ctx.function.Blocks, ctx.StructArgumentWidths);
        });
        ctx.Passes.Run("prepare.TrimIndirectArguments", () =>
        {
            ctx.TrimIndirectArguments();
        });
        ctx.Passes.Run("prepare.Cpp2CS.Machine.Ssa.Propagate.RemoveDead", () =>
        {
            Cpp2CS.Machine.Ssa.Propagate.RemoveDead(ctx.function);
        });
        // 库内存操作归一后也可能产生新栈读写；普通方法与异常方法采用同一有界提升规则。
        ctx.Passes.Run("prepare.FrameWritebacks.Run", () =>
        {
            FrameWritebacks.Run(ctx.function);
        });
        var constantFrameIndices = FrameConstantIndices.Run(ctx.function) > 0;
        ctx.Passes.Run("prepare.ManagedFramePromotion.Run", () =>
        {
            ManagedFramePromotion.Run(ctx.facts, ctx.function, ctx.owner.abi, ctx.owner.lifter.Calls, ctx.owner.lifter.Machine.Convention.StackPointer, signature.Return);
        });
        ctx.Passes.Run("prepare.Cpp2CS.Machine.Ssa.Propagate.Run", () =>
        {
            if (constantFrameIndices)
            {
                Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
                ctx.PromotePrivateFrameSlots();
            }
        });
        ctx.Passes.Run("prepare.NormalizeCleanupThunks", () =>
        {
            ctx.NormalizeCleanupThunks();
        });
        ctx.Passes.Run("prepare.NormalizeOutlinedCalls", () =>
        {
            ctx.NormalizeOutlinedCalls(idioms);
        });
        // 清理 thunk 拆开后，栈上的 this 可回代为参数；用同一套委托证明消费新出现的类型证据。
        ctx.Passes.Run("prepare.DelegateCallNormalizer.Run", () =>
        {
            if (DelegateCallNormalizer.Run(ctx.facts, ctx.function, idioms))
            {
                ctx.function.Problems.AddRange(Cpp2CS.Machine.Ssa.Lowering.Cleanup(ctx.function));
                var delegates = ctx.function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c is { Op.Kind: OpKind.CallDelegate, Target: Symbol { Kind: SymbolKind.Method }, DelegateReceiver: not null }).Select(c => c.Address).ToHashSet();
                idioms.Residuals.RemoveAll(r => r.Category.StartsWith("indirect:", StringComparison.Ordinal) && delegates.Contains(r.Address));
            }
        });
        ctx.Passes.Run("prepare.function.Blocks.Any", () =>
        {
            if (ctx.function.Blocks.Any(b => b.IsLandingPad))
                while (ExceptionNullBranches.Run(ctx.facts, ctx.function))
                    ctx.function.Problems.AddRange(Cpp2CS.Machine.Ssa.Lowering.Cleanup(ctx.function));
        });
        foreach (var residual in idioms.Residuals)
        {
            // 写屏障实参裁剪后，部分 Class 读取已被 SSA 证明无使用；旧 L2 诊断不再对应活语句。
            if (residual.Category.StartsWith("load:Class+", StringComparison.Ordinal) && ctx.function.Dead.Any(p => p.Define.Address == residual.Address && ExprMap.Walk(p.Define.Value).OfType<Load>().Any(l => ExprMap.Walk(l.Address).Any(e => e is Symbol { Kind: SymbolKind.Class }))) && !ctx.function.Blocks.SelectMany(b => b.Statements).Any(s => s.Address == residual.Address))
            {
                ctx.ruleTraces.Add(new("runtime.dead-class-read", residual.Address, RewriteStatus.Applied, "runtime.unused-class-metadata", "Class 读取的全部使用已由 SSA 消除，保留原诊断与死定义证据", new("ssa.dead-definition", [residual.Address], [residual.Category, residual.Detail])));
                continue;
            }

            // 没有身份证据的未注册调用交给 L3 的调用解析（方法的本地副本，CopyOf）；解析不了时在调用处留洞。
            if (residual.Category is not ("helper:WriteBarrier" or "call:unregistered-managed") && !ctx.State.Calls.cleanupSites.Contains(residual.Address) && !ctx.State.Calls.sharedSites.Contains(residual.Address))
            {
                var hole = ctx.Hole(residual.Address, $"残余 {residual.Category}", rule: "Prepare");
                foreach (var statement in ctx.function.Blocks.SelectMany(b => b.Statements).Where(s => s.Address == residual.Address))
                    ctx.ledger.Block(statement, hole);
            }
        }

        ctx.blocks = ctx.function.Blocks;
        if (ctx.function.Blocks.FirstOrDefault(b => b.IsLandingPad) is { } landing && !ctx.PrepareExceptionRegions())
        {
            var hole = ctx.Hole(landing.Start, $"异常区域 {ctx.State.Exceptions.exceptionLayout?.Reason ?? "尚未恢复"} {ctx.State.Exceptions.exceptionLayout?.Detail}", rule: "Prepare");
            // Handler 是受保护块的异常后继，不能把受保护块本身排除。只保留入口的正常边闭包。
            var normal = new HashSet<Block>();
            var pending = new Stack<Block>();
            pending.Push(ctx.function.EntryBlock);
            while (pending.TryPop(out var block))
                if (!block.IsLandingPad && normal.Add(block))
                    foreach (var successor in block.NormalSuccessors)
                        pending.Push(successor);
            ctx.blocks = ctx.function.Blocks.Where(normal.Contains).ToArray();
            foreach (var statement in ctx.function.Blocks.Where(b => !normal.Contains(b)).SelectMany(b => b.Statements))
            {
                ctx.Poison(statement, hole);
                if (statement is Phi phi)
                    ctx.Poison(phi.Target, hole);
            }
        }

        foreach (var problem2 in ctx.function.Problems)
            ctx.Hole(ctx.entry, $"控制流 {problem2}", rule: "Prepare");
        return true;
    }
}
