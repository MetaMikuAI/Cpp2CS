using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Ssa;

/// <summary>将合并尾部放回入边，流出结果经出口 φ 汇合，保留每条路径的操作次序。</summary>
internal static class TailDuplication
{
    internal static bool Run(MachineFunction function, Func<Block, bool> select, bool keepResults = false)
    {
        static IEnumerable<Variable> Defines(Stmt statement) => statement switch
        {
            Phi p => [p.Target], Define d => [d.Target], Call c => c.Defines.OfType<Variable>(), _ => [],
        };
        var versions = function.Blocks.SelectMany(b => b.Statements).SelectMany(Defines).GroupBy(v => v.Storage)
            .ToDictionary(g => g.Key, g => g.Max(v => v.Version) + 1);
        Variable Fresh(Variable variable) => variable with { Version = versions[variable.Storage]++ };
        var changed = false;
        foreach (var merge in function.Blocks.ToArray())
        {
            if (!function.Blocks.Contains(merge) || merge.Handler is not null || merge.IsLandingPad
                || merge.Predecessors.Count is < 2 or > 16 || merge.Statements.Count > 96 || !select(merge)
                || merge.Statements.Any(s => s is not (Phi or Define or Store or Call or Jump or Nop or Return))) continue;
            var exits = merge.NormalSuccessors.ToArray();
            if (exits.Length > 1 || exits.Length == 0 && merge.Statements.LastOrDefault() is not (Return or Call { Kind: CallKind.Tail or CallKind.TailIndirect })) continue;
            var exit = exits.SingleOrDefault();
            var incoming = merge.Predecessors.ToArray();
            if (incoming.Distinct().Count() != incoming.Length || incoming.Any(p => p == merge || p == exit || p.Handler is not null || p.IsLandingPad
                || p.NormalSuccessors.ToArray() is not [var next] || next != merge || p.Statements.LastOrDefault() is Branch)) continue;
            var defined = merge.Statements.SelectMany(Defines).ToHashSet();
            var exitIndex = exit?.Predecessors.IndexOf(merge) ?? -1;
            var external = function.Blocks.Where(b => b != merge).SelectMany(b => b.Statements).SelectMany(s => s is Phi phi
                ? phi.Sources : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable))
                .Where(defined.Contains).Distinct().ToArray();
            var keepJoin = function.Blocks.Where(b => b != merge).Any(b => b.Statements.Any(s => s is Phi phi
                ? phi.Sources.Where((_, i) => b != exit || i != exitIndex).Any(defined.Contains)
                : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => defined.Contains(u.Variable))));
            if (keepJoin && (!keepResults || exit is null)) continue;
            // 保留的结果汇合不可重复展开；可消除的纯 φ 块仍需转接到出口，暴露各入边的类型身份。
            if (keepJoin && merge.Statements.All(s => s is Phi or Jump or Nop)) continue;
            // 调用结果或其他合流值仍被后续使用时，原块只保留结果 φ，不复制后续业务语句。
            var joined = (keepJoin ? external : []).ToDictionary(v => v, _ => new List<Variable>());
            var exitValues = exit?.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[exitIndex]);
            var statements = merge.Statements.ToArray();
            var phis = statements.OfType<Phi>().ToArray();
            if (phis.Any(p => p.Sources.Length != incoming.Length)) continue;
            for (var side = 0; side < incoming.Length; side++)
            {
                var parent = incoming[side];
                var map = phis.ToDictionary(p => p.Target, p => p.Sources[side]);
                parent.Statements.RemoveAll(s => s is Jump);
                foreach (var statement in statements.Where(s => s is not (Phi or Jump)))
                {
                    var mapped = ExprMap.MapOperands(statement, e => ExprMap.Map(e,
                        value => value is Use u && map.TryGetValue(u.Variable, out var replacement) ? new Use(replacement, u.Width) : null));
                    if (mapped is Define d)
                    {
                        var variable = Fresh(d.Target); map[d.Target] = variable;
                        mapped = d with { Target = variable };
                    }
                    else if (mapped is Call call)
                    {
                        var variables = call.Defines.Select(v => v is null ? null! : Fresh(v)).ToArray();
                        for (var i = 0; i < variables.Length; i++) if (call.Defines[i] is { } old) map[old] = variables[i];
                        mapped = call with { Defines = variables };
                    }
                    parent.Statements.Add(mapped);
                }
                if (joined.Count > 0)
                {
                    foreach (var (variable, sources) in joined) sources.Add(map.GetValueOrDefault(variable, variable));
                    parent.Statements.Add(new Jump(parent.End, merge.Start));
                    continue;
                }
                MachineFunction.RemoveEdgeAt(parent, parent.Successors.IndexOf(merge));
                if (exit is null) continue;
                MachineFunction.AddEdge(parent, exit);
                parent.Statements.Add(new Jump(parent.End, exit.Start));
                for (var i = 0; i < exit.Statements.Count && exit.Statements[i] is Phi phi; i++)
                {
                    var source = exitValues![phi.Target];
                    exit.Statements[i] = phi with { Sources = [.. phi.Sources, map.GetValueOrDefault(source, source)] };
                }
            }
            if (joined.Count > 0)
                merge.Statements = [.. joined.Select(p => (Stmt)new Phi(merge.Start, p.Key, p.Value.ToArray())), new Jump(merge.End, exit!.Start)];
            function.Renumber();
            changed = true;
        }
        return changed;
    }
}
