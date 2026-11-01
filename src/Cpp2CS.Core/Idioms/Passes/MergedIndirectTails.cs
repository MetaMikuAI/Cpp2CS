using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>只有参数合流的间接或泛型尾调用回放到各自入边，保持接收者与方法身份配对。</summary>
internal static class MergedIndirectTails
{
    public static bool Run(MachineFunction function)
    {
        var changed = false;
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        foreach (var merge in function.Blocks.ToArray())
        {
            if (merge.Handler is not null || merge.IsLandingPad || merge.NormalSuccessors.Any() || merge.Predecessors.Count < 2
                || merge.Statements.Where(s => s is not (Phi or Nop)).ToArray() is not
                    [Call { Kind: CallKind.TailIndirect or CallKind.Tail, Op: null, Defines.Length: 0 } call]) continue;
            var phis = merge.Statements.OfType<Phi>().ToArray();
            var incoming = merge.Predecessors.ToArray();
            var defined = phis.Select(p => p.Target).ToHashSet();
            var indirect = call.Kind == CallKind.TailIndirect && call.Target is Use target && defined.Contains(target.Variable);
            var generic = call.Kind == CallKind.Tail && call.Target is Const && call.Arguments.OfType<Use>().Any(argument =>
            {
                var phi = phis.FirstOrDefault(p => p.Target == argument.Variable);
                if (phi is null || phi.Sources.Length == 0) return false;
                var methods = phi.Sources.Select(v => definitions.GetValueOrDefault(v)).OfType<Symbol>()
                    .Where(s => s.Kind == SymbolKind.Method).Select(s => s.Value).OfType<MethodRef>().ToArray();
                return methods.Length == phi.Sources.Length && methods.Select(m => m.Method).Distinct().Count() == 1
                    && methods.All(m => m.TypeArguments.Count + m.MethodArguments.Count > 0);
            });
            if (!indirect && !generic || phis.Any(p => p.Sources.Length != incoming.Length || p.Sources.Any(defined.Contains))
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
