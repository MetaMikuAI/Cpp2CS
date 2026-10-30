using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class ZeroPhiSourcesPass
{
    internal static bool ZeroPhiSources(this IdiomState state)
    {
        var dominators = Dominators.Compute(state.function);
        var zeros = new List<(Variable Value, Block From, Block To)>();
        foreach (var block in state.function.Blocks)
            if (block.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use { Width: 64 } value, Right: Const { Value: 0 } } test } branch && block.NormalSuccessors.FirstOrDefault(b => b.Start == (test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough)) is { } target)
                zeros.Add((value.Variable, block, target));
        var changed = false;
        foreach (var block in state.function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().ToArray())
            {
                var sources = phi.Sources.ToArray();
                for (var i = 0; i < sources.Length; i++)
                {
                    var parent = block.Predecessors[i];
                    if (!zeros.Any(z => z.Value == sources[i] && (z.From == parent && z.To == block || z.To.Predecessors.Count == 1 && dominators.Dominates(z.To.Index, parent.Index))))
                        continue;
                    sources[i] = state.Fresh();
                    var terminal = parent.Statements.LastOrDefault();
                    parent.Statements.Insert(parent.Statements.Count - (terminal is Jump or Branch or IndirectJump or Return ? 1 : 0), new Define(terminal?.Address ?? parent.Start, sources[i], Expr.C(0, 64)));
                    changed = true;
                }

                block.Statements[block.Statements.IndexOf(phi)] = phi with
                {
                    Sources = sources
                };
            }

        return changed;
    }
}
