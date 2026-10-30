using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class FlagPhiConditionsPass
{
    internal static bool FlagPhiConditions(this IdiomState state)
    {
        var changed = false;
        foreach (var block in state.function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().Where(p => p.Target.Storage.Bank == Bank.Flags).ToArray())
            {
                var tests = state.All.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<TestFlags>().Where(t => t.FlagsValue is Use u && u.Variable == phi.Target).Distinct().ToArray();
                foreach (var test in tests)
                {
                    var conditions = phi.Sources.Select(v => Fold.TestFlags(state.defs.Expand(new Use(v, 0)), test.Code)).ToArray();
                    if (conditions.Any(c => ExprMap.Walk(c).Any(e => e is TestFlags or Flags or ConditionalFlags or Unknown or Load)))
                        continue;
                    var result = state.Fresh();
                    var inputs = conditions.Select(_ => state.Fresh()).ToArray();
                    for (var p = 0; p < inputs.Length; p++)
                    {
                        var pred = block.Predecessors[p];
                        var index = pred.Statements.Count - (pred.Statements.LastOrDefault() is Jump or Branch ? 1 : 0);
                        pred.Statements.Insert(index, new Define(phi.Address, inputs[p], conditions[p]));
                    }

                    block.Statements.Insert(0, new Phi(phi.Address, result, inputs));
                    foreach (var current in state.function.Blocks)
                        for (var i = 0; i < current.Statements.Count; i++)
                            current.Statements[i] = ExprMap.MapOperands(current.Statements[i], e => ExprMap.Map(e, x => x.Equals(test) ? new Use(result, 1) : null));
                    changed = true;
                }
            }

        return changed;
    }
}
