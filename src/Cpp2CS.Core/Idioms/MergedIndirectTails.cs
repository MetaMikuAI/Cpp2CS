using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>只有参数合流的间接尾调用回放到各自入边，分别识别调用来源。</summary>
internal static class MergedIndirectTails
{
    public static bool Run(MachineFunction function)
    {
        var changed = false;
        foreach (var merge in function.Blocks.ToArray())
        {
            if (merge.Handler is not null || merge.IsLandingPad || merge.NormalSuccessors.Any() || merge.Predecessors.Count < 2
                || merge.Statements.Where(s => s is not (Phi or Nop)).ToArray() is not
                    [Call { Kind: CallKind.TailIndirect, Op: null, Target: Use target, Defines.Length: 0 } call]) continue;
            var phis = merge.Statements.OfType<Phi>().ToArray();
            var incoming = merge.Predecessors.ToArray();
            var defined = phis.Select(p => p.Target).ToHashSet();
            if (!defined.Contains(target.Variable) || phis.Any(p => p.Sources.Length != incoming.Length || p.Sources.Any(defined.Contains))
                || incoming.Distinct().Count() != incoming.Length || incoming.Any(p => p == merge || p.Handler is not null || p.IsLandingPad
                    || p.NormalSuccessors.ToArray() is not [var next] || next != merge
                    || p.Statements.LastOrDefault() is Branch or Call { Kind: CallKind.Tail or CallKind.TailIndirect })
                || function.Blocks.Where(b => b != merge).SelectMany(b => b.Statements).Any(s => s is Phi phi && phi.Sources.Any(defined.Contains)
                    || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => defined.Contains(u.Variable)))) continue;
            for (var side = 0; side < incoming.Length; side++)
            {
                var predecessor = incoming[side];
                var map = phis.ToDictionary(p => p.Target, p => p.Sources[side]);
                var mapped = ExprMap.MapOperands(call, e => ExprMap.Map(e,
                    value => value is Use use && map.TryGetValue(use.Variable, out var source) ? new Use(source, use.Width) : null));
                if (predecessor.Statements.LastOrDefault() is Jump) predecessor.Statements.RemoveAt(predecessor.Statements.Count - 1);
                predecessor.Statements.Add(mapped);
                MachineFunction.RemoveEdge(predecessor, merge);
            }
            changed = true;
        }
        if (changed) function.Renumber();
        return changed;
    }
}
