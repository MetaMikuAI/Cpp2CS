using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class MergePass
{
    internal static Dictionary<Variable, Variable>? Merge(this IdiomState state, Block head, List<Block> chain, Block merge, Expr? resultEquals, Func<Variable, Variable?>? reload)
    {
        var regionIndex = merge.Predecessors.IndexOf(chain[^1]);
        var headIndex = merge.Predecessors.IndexOf(head);
        var regionDefined = DefinedPass.Defined(chain);
        var overrides = new Dictionary<Variable, Variable>();
        foreach (var phi in merge.Statements.OfType<Phi>())
        {
            Variable inside = phi.Sources[regionIndex], skipped = phi.Sources[headIndex];
            if (inside == skipped || !regionDefined.Contains(inside))
                continue;
            var call = chain.SelectMany(b => b.Statements).OfType<Call>().FirstOrDefault(c => c.Defines.Contains(inside));
            if (call is not null && resultEquals is not null && call.Defines[0] == inside)
            {
                if (state.defs.Expand(new Use(skipped, 64)) != resultEquals)
                {
                    if (state.Used(phi.Target))
                        return null;
                    overrides[phi.Target] = new Variable(phi.Target.Storage, -1);
                }

                continue;
            }

            if (call is null && reload?.Invoke(inside) is { } fresh)
            {
                overrides[phi.Target] = fresh;
                continue;
            }

            if (call is null && state.defs.Expand(new Use(inside, 64)) == state.defs.Expand(new Use(skipped, 64)))
                continue;
            if (state.Used(phi.Target))
                return null;
            overrides[phi.Target] = new Variable(phi.Target.Storage, -1);
        }

        return overrides;
    }
}
