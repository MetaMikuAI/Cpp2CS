using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class KnownMetadataGuardsPass
{
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
