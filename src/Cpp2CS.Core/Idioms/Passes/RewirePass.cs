using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class RewirePass
{
    internal static bool Rewire(this IdiomState state, Block head, List<Stmt> insert, Stmt terminator, List<(Block To, Block Via)> targets, List<Block> region)
    {
        var regionDefined = DefinedPass.Defined(region);
        var operands = new List<Variable[]>();
        foreach (var (to, via) in targets)
        {
            var index = to.Predecessors.IndexOf(via);
            if (index < 0)
                return false;
            var phis = to.Statements.TakeWhile(s => s is Phi).Cast<Phi>().ToArray();
            var row = new Variable[phis.Length];
            for (var i = 0; i < phis.Length; i++)
            {
                var source = phis[i].Sources[index];
                if (regionDefined.Contains(source))
                {
                    if (state.Used(phis[i].Target))
                        return false;
                    source = new Variable(source.Storage, -1);
                }

                row[i] = source;
            }

            operands.Add(row);
        }

        for (var k = head.NormalSuccessors.Count() - 1; k >= 0; k--)
            MachineFunction.RemoveEdgeAt(head, k);
        head.Statements.RemoveAt(head.Statements.Count - 1);
        head.Statements.AddRange(insert);
        head.Statements.Add(terminator);
        for (var t = 0; t < targets.Count; t++)
        {
            var to = targets[t].To;
            MachineFunction.AddEdge(head, to);
            for (var i = 0; i < operands[t].Length; i++)
            {
                var phi = (Phi)to.Statements[i];
                to.Statements[i] = phi with
                {
                    Sources = [.. phi.Sources, operands[t][i]]
                };
            }
        }

        return true;
    }
}
