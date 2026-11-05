using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class KnownMetadataGuardsPass
{
    /// <summary>
    /// 写入标志字节的值在路径条件下等于 1 时，寄存器分配可复用持有 1 的寄存器。还原成常量，守卫证明才能看到写入的是 1。
    /// </summary>
    internal static bool GuardFlagValues(this IdiomState state)
    {
        var writes = state.function.Blocks.SelectMany(b => b.Statements.Select(s => (Block: b, Statement: s)))
            .Where(w => w.Statement is Store { Target: Const, Value: Use { Width: 8 } }).ToArray();
        if (writes.Length == 0) return false;
        var dominators = Dominators.Compute(state.function);
        bool KnownOne(Variable value, Block at) => state.function.Blocks.Any(b =>
            b.Statements.LastOrDefault() is Branch branch
            && Fold.Simplify(branch.Condition) is Compare { Cond: Cond.Eq or Cond.Ne, Left: Use compared, Right: Const { Value: 1 } } test && compared.Variable == value
            && b.NormalSuccessors.FirstOrDefault(s => s.Start == (test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough)) is { Predecessors.Count: 1 } taken
            && dominators.Dominates(taken.Index, at.Index));
        var changed = false;
        foreach (var (block, statement) in writes)
        {
            var store = (Store)statement;
            if (!KnownOne(((Use)store.Value).Variable, block)) continue;
            block.Statements[block.Statements.IndexOf(store)] = store with { Value = Expr.C(1, 8) };
            changed = true;
        }
        return changed;
    }

    internal static bool KnownMetadataGuards(this IdiomState state)
    {
        if (state.initializedGuards.Count == 0)
            return false;
        var dominators = Dominators.Compute(state.function);
        var seeds = state.initializedGuards.Where(p => state.function.Blocks.Contains(p.End) && !state.removed.Contains(p.End) && !state.All.OfType<Store>().Any(s => s.Target is Const target && target.Value == p.Guard && s.Value is not Const { Value: 1, Width: 8 })).ToArray();
        var changed = false;
        foreach (var block in state.function.Blocks.Where(b => !state.removed.Contains(b)))
        {
            var known = seeds.Where(p => p.End != block && dominators.Dominates(p.End.Index, block.Index)).Select(p => p.Guard).ToHashSet();
            if (known.Count == 0)
                continue;
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var previous = block.Statements[i];
                var replacement = previous is Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } store && known.Contains(target.Value) ? new Nop(store.Address, "MetadataInitGuard") : ExprMap.MapOperands(previous, e => ExprMap.Map(e, part => part is Load { Width: 8, Address: Const address } && known.Contains(address.Value) ? Expr.C(1, 8) : null));
                if (replacement == previous)
                    continue;
                block.Statements[i] = replacement;
                changed = true;
            }
        }

        return changed;
    }
}
