using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class CleanupThunksRules
{
    internal static void NormalizeCleanupThunks(this RecoveryScope ctx)
    {
        foreach (var block in ctx.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null, Target: Const target, Arguments.Length: > 0 } call || ctx.owner.NativeMethods.CleanupThunk(target.Value, ctx.method.Method.Owner) is not { } thunk)
                    continue;
                Expr receiver = call.Arguments[0];
                for (var n = 0; n < thunk.Depth; n++)
                    receiver = new Load(receiver, 64);
                var replacement = call with
                {
                    Target = Expr.C(thunk.Method.Method.Address, 64),
                    Arguments = [receiver, Expr.C(0, 64)],
                    Sources = [Storage.Gpr(0), Storage.Gpr(1)],
                    Results = [],
                    Defines = []
                };
                ctx.Rewriter.Replace(block, i, replacement);
                ctx.State.Calls.cleanupCalls.Add(replacement);
                ctx.State.Calls.cleanupSites.Add(call.Address);
                if (thunk.Inlined)
                    ctx.State.Calls.inlineCleanupSites.Add(call.Address);
            }

        if (ctx.State.Calls.cleanupCalls.Count == 0)
            return;
        ctx.PromotePrivateFrameSlots();
        Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
        ctx.State.Calls.cleanupCalls.Clear();
        ctx.State.Calls.cleanupCalls.UnionWith(ctx.function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => ctx.State.Calls.cleanupSites.Contains(c.Address)));
    }

    internal static void PromotePrivateFrameSlots(this RecoveryScope ctx)
    {
        var all = ctx.function.Blocks.SelectMany(b => b.Statements).ToArray();
        var stores = all.OfType<Store>().Where(s => s.Target is FrameAddress).GroupBy(s => ((FrameAddress)s.Target).Offset).Where(g => g.Count() == 1 && g.Single().Value.Width == 64).ToDictionary(g => g.Key, g => g.Single());
        var positions = ctx.function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (s, b, i))).ToDictionary(p => p.s, p => (p.b, p.i), (IEqualityComparer<Stmt>)ReferenceEqualityComparer.Instance);
        bool Dominates(Store store, Stmt use)
        {
            var (from, i) = positions[store];
            var (to, j) = positions[use];
            if (from == to)
                return i < j;
            var visited = new HashSet<Block>();
            var pending = new Stack<Block>();
            pending.Push(ctx.function.EntryBlock);
            while (pending.TryPop(out var b))
            {
                if (b == from || !visited.Add(b))
                    continue;
                if (b == to)
                    return false;
                foreach (var next in b.Successors)
                    pending.Push(next);
            }

            return true;
        }

        bool Safe(Expr e, long offset) => e switch
        {
            Load { Address: FrameAddress f } load when f.Offset < offset + 8 && f.Offset + load.Width / 8 > offset => f.Offset == offset && load.Width == 64,
            FrameAddress f when f.Offset < offset + 8 => false,
            _ => ExprMap.Children(e).All(p => Safe(p, offset))
        };
        var frames = new ManagedCallFrames(ctx.facts, ctx.owner.abi);
        int? ArgumentExtent(Call call, int index)
        {
            if (call.Op is not { Kind: OpKind.InvokeGeneric, Operand: MethodRef callee })
                return frames.ArgumentSize(call, index);
            if (index == 0)
                return null;
            var type = index == call.Arguments.Length - 1 ? CallResolution.Concrete(callee, callee.Method.ReturnType) : CallResolution.Concrete(callee, callee.Method.Parameters[index - 1].Type);
            return ctx.types.Size(type) is > 0 and var size ? size : null;
        }

        bool Touches(Stmt statement, long offset, int bytes) => FrameUses.Touches(statement, offset, bytes, ArgumentExtent);
        var promotable = stores.Where(pair => pair.Value.Value is FrameAddress or Use { Variable.Version: 0 } && all.Where(s => !ReferenceEquals(s, pair.Value)).All(s => !Touches(s, pair.Key, 8) || Dominates(pair.Value, s) && (s is Store { Target: FrameAddress dest, Value: FrameAddress source } && source.Offset == pair.Key && stores.ContainsKey(dest.Offset) || ExprMap.Operands(s).All(e => Safe(e, pair.Key))))).ToDictionary(p => p.Key, p => p.Value);
        Expr Expand(Expr e, int depth = 0)
        {
            if (depth > 8)
                return e;
            var mapped = ExprMap.Map(e, p => p is Load { Address: FrameAddress f, Width: 64 } && promotable.TryGetValue(f.Offset, out var store) ? store.Value : null);
            return mapped == e ? e : Expand(mapped, depth + 1);
        }

        foreach (var block in ctx.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                var mapped = ExprMap.MapOperands(old, e => Expand(e));
                ctx.Rewriter.Replace(block, i, mapped);
                if (old is Call call && ctx.State.Calls.cleanupCalls.Remove(call))
                    ctx.State.Calls.cleanupCalls.Add((Call)mapped);
            }

        // 仅删除不再被读取或取址的局部写入。
        foreach (var group in ctx.function.Blocks.SelectMany(b => b.Statements).OfType<Store>().Where(s => s.Target is FrameAddress).GroupBy(s => ((FrameAddress)s.Target).Offset).ToArray())
        {
            var writes = group.ToHashSet();
            if (group.Select(s => s.Value.Width).Distinct().ToArray() is not [var width] || group.Any(s => ExprMap.Walk(s.Value).Any(e => e is Load or Intrinsic or Unknown)) || ctx.function.Blocks.SelectMany(b => b.Statements).Where(s => s is not Store store || !writes.Contains(store)).Any(s => Touches(s, group.Key, width / 8)))
                continue;
            foreach (var block in ctx.function.Blocks)
                ctx.Rewriter.RemoveAll(block, s => s is Store store && writes.Contains(store));
        }

        bool changed;
        do
        {
            changed = false;
            foreach (var block in ctx.function.Blocks)
                foreach (var store in block.Statements.OfType<Store>().Where(s => s.Target is FrameAddress).ToArray())
                {
                    var frame = (FrameAddress)store.Target;
                    if (ExprMap.Walk(store.Value).Any(e => e is Load or Intrinsic or Unknown))
                        continue;
                    if (ctx.function.Blocks.SelectMany(b => b.Statements).Where(s => !ReferenceEquals(s, store)).Any(s => Touches(s, frame.Offset, store.Value.Width / 8)))
                        continue;
                    ctx.Rewriter.Remove(block, store);
                    changed = true;
                }
        }
        while (changed);
    }

    [CallRule(10)]
    internal static RecoveryResult<bool> LowerCleanupThunk(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (!ctx.State.Calls.cleanupCalls.Contains(call))
            return false;
        var callee = ctx.facts.EntriesAt(((Const)call.Target).Value).Select(e => e.Method).OfType<MethodRef>().Single();
        if (!ctx.Values.RecoverAs(call.Arguments[0], callee.DeclaringType, call.Address).TryGet(out var receiver, out var failure))
            return failure;
        output.Add(new ManagedCall(call.Address, new ManagedInvocation(callee, receiver, [], false), null, false) { Inlined = ctx.State.Calls.inlineCleanupSites.Contains(call.Address) });
        return true;
    }
}
