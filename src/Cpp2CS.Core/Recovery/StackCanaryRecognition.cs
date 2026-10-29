using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>识别线程栈保护值的保存、比较和唯一失败出口。</summary>
internal static class StackCanaryRecognition
{
    internal static int Run(MachineFunction function, Func<Expr, int, Expr>? expand = null, Func<Call, int, int?>? extent = null)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr e, int depth = 0) => depth > 24 ? e : ExprMap.Map(e,
            p => p is Use u && definitions.TryGetValue(u.Variable, out var value) ? Expand(value, depth + 1) : null);
        expand ??= Expand;
        var stores = function.Blocks.SelectMany(b => b.Statements).OfType<Store>().ToArray();
        var single = stores.Where(s => s.Target is FrameAddress).GroupBy(s => (FrameAddress)s.Target)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        bool Intact(FrameAddress slot, Store saved) => saved.Value.Width == 64 && !stores.Any(s => !ReferenceEquals(s, saved)
            && s.Target is FrameAddress at && at.Offset < slot.Offset + 8 && slot.Offset < at.Offset + s.Value.Width / 8);
        bool Thread(Expr e) => e is Intrinsic { Name: "sysreg_tpidr_el0", Arguments.Length: 0 }
            || e is Load { Width: 64, Address: FrameAddress slot } && single.TryGetValue(slot, out var saved)
                && Intact(slot, saved)
                && expand(saved.Value, 0) is Intrinsic { Name: "sysreg_tpidr_el0", Arguments.Length: 0 };
        bool Canary(Expr e) => expand(e, 0) is Load { Width: 64, Address: Binary { Op: BinOp.Add,
            Left: var thread, Right: Const { Value: 0x28 } } } && Thread(thread);
        var changed = 0;
        var guards = new HashSet<Store>(ReferenceEqualityComparer.Instance);
        foreach (var block in function.Blocks.ToArray())
        {
            if (block.Statements.LastOrDefault() is not Branch branch || expand(branch.Condition, 0) is not Compare
                { Cond: Cond.Ne or Cond.Eq } comparison || block.NormalSuccessors.ToArray() is not [var taken, var fallthrough]) continue;
            var fail = comparison.Cond == Cond.Ne ? taken : fallthrough;
            var normal = comparison.Cond == Cond.Ne ? fallthrough : taken;
            if (taken.Start != branch.Target || fallthrough.Start != branch.Fallthrough || fail.Handler is not null
                || fail.Statements.Where(s => s is not Nop).ToArray() is not [Call { Op: { Kind: OpKind.Import, Operand: "__stack_chk_fail" } }]) continue;
            var left = comparison.Left;
            var right = comparison.Right;
            if (!Canary(left)) (left, right) = (right, left);
            if (!Canary(left) || right is not Load { Width: 64, Address: FrameAddress { Offset: < 0 } slot }
                || !single.TryGetValue(slot, out var saved) || saved.Value.Width != 64 || !Canary(saved.Value)) continue;
            if (!Intact(slot, saved)) continue;
            bool Escapes(Expr e) => e switch
            {
                Load { Address: FrameAddress } => false,
                FrameAddress at => at.Offset < slot.Offset + 8,
                _ => ExprMap.Children(e).Any(Escapes),
            };
            if (function.Blocks.SelectMany(b => b.Statements).Any(s => s switch
            {
                Store { Target: FrameAddress } store => Escapes(store.Value),
                Call call => FrameUses.Touches(call, slot.Offset, 8, extent ?? ((_, _) => null)),
                _ => ExprMap.Operands(s).Any(Escapes),
            })) continue;
            var savedBlock = function.Blocks.Single(b => b.Statements.Contains(saved));
            var dominators = Ssa.Dominators.Compute(function);
            if (!dominators.Dominates(savedBlock.Index, block.Index)
                || savedBlock == block && savedBlock.Statements.IndexOf(saved) >= savedBlock.Statements.Count - 1) continue;
            block.Statements[^1] = new Jump(branch.Address, normal.Start);
            MachineFunction.RemoveEdgeAt(block, comparison.Cond == Cond.Ne ? 0 : 1);
            guards.Add(saved);
            changed++;
        }
        if (changed > 0)
        {
            function.Problems.AddRange(Ssa.Lowering.Cleanup(function));
            foreach (var saved in guards)
            {
                var slot = (FrameAddress)saved.Target;
                if (function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk)
                    .OfType<Load>().Any(l => l.Address is FrameAddress at && at.Offset < slot.Offset + 8 && slot.Offset < at.Offset + l.Width / 8)) continue;
                foreach (var block in function.Blocks) block.Statements.Remove(saved);
            }
            Ssa.Propagate.RemoveDead(function);
        }
        return changed;
    }
}
