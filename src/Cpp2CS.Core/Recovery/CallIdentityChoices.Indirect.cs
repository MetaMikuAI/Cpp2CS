using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static partial class CallIdentityChoices
{
    // 编译器合并的间接调用移回各入边，保留函数指针、实例、参数与结果的对应关系。
    internal static bool SplitIndirect(MachineFunction function)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        var versions = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
        {
            Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines, _ => [],
        }).Where(v => v is not null).GroupBy(v => v.Storage).ToDictionary(g => g.Key, g => g.Max(v => v.Version) + 1);
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.IsLandingPad || block.Predecessors.Count is < 2 or > 4 || block.Predecessors.Any(p => p == block || p.Handler is not null
                || p.NormalSuccessors.ToArray() is not [var next] || next != block)) continue;
            var phis = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            if (phis.Values.Any(p => p.Sources.Length != block.Predecessors.Count)) continue;
            var prefix = block.Statements.Where(s => s is not (Phi or Nop)).TakeWhile(s => s is Define).Cast<Define>().ToArray();
            if (prefix.Length > 16 || block.Statements.FirstOrDefault(s => s is not (Phi or Nop or Define))
                is not Call { Op: null, Kind: CallKind.Indirect } call || call.Defines.Any(v => v is null)) continue;
            var definitions = prefix.ToDictionary(d => d.Target, d => d.Value);
            bool Selected(Expr expression, HashSet<Variable> seen) => ExprMap.Walk(expression).OfType<Use>().Any(u =>
                phis.ContainsKey(u.Variable) || seen.Add(u.Variable) && definitions.TryGetValue(u.Variable, out var source) && Selected(source, seen));
            if (!Selected(call.Target, [])) continue;
            var moved = prefix.Select(d => d.Target).Concat(call.Defines).ToArray();
            if (moved.Distinct().Count() != moved.Length || phis.Values.Any(p => p.Sources.Any(moved.Contains))) continue;
            var joined = moved.ToDictionary(v => v, _ => new List<Variable>());
            for (var side = 0; side < block.Predecessors.Count; side++)
            {
                var replacements = moved.ToDictionary(v => v, v => v with { Version = versions[v.Storage]++ });
                foreach (var variable in moved) joined[variable].Add(replacements[variable]);
                Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use
                    ? phis.TryGetValue(use.Variable, out var phi) ? new Use(phi.Sources[side], use.Width)
                        : replacements.TryGetValue(use.Variable, out var renamed) ? new Use(renamed, use.Width) : null : null);
                var parent = block.Predecessors[side];
                var position = parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump ? 1 : 0);
                foreach (var define in prefix)
                    parent.Statements.Insert(position++, define with { Target = replacements[define.Target], Value = OnEdge(define.Value) });
                parent.Statements.Insert(position, ((Call)ExprMap.MapOperands(call, OnEdge)) with
                    { Defines = call.Defines.Select(v => replacements[v]).ToArray() });
            }
            foreach (var define in prefix) block.Statements.Remove(define);
            block.Statements.Remove(call);
            block.Statements.InsertRange(0, moved.Select(v => new Phi(call.Address, v, joined[v].ToArray())));
            changed = true;
        }
        return changed;
    }
}
