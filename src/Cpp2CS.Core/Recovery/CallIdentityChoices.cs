using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>方法身份随分支变化的共用调用，沿原入边保留身份、实参与结果的对应关系。</summary>
internal static partial class CallIdentityChoices
{
    internal static bool SplitGeneric(MachineFunction function, Func<Call, int, MethodRef, bool> identity, Func<Expr, Expr> expand)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        var changed = false;
        var versions = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
        {
            Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines, _ => [],
        }).Where(v => v is not null).GroupBy(v => v.Storage).ToDictionary(g => g.Key, g => g.Max(v => v.Version) + 1);
        foreach (var block in function.Blocks)
        {
            if (block.IsLandingPad || block.Predecessors.Count < 2 || block.Predecessors.Any(p => p == block || p.Handler is not null
                || p.NormalSuccessors.ToArray() is not [var next] || next != block)) continue;
            var phis = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            if (block.Statements.FirstOrDefault(s => s is not (Phi or Nop)) is not Call { Op: null, Kind: CallKind.Direct, Target: Const } call) continue;
            var selected = call.Arguments.Select((argument, index) => (argument, index)).Any(pair => pair.argument is Use use
                && phis.TryGetValue(use.Variable, out var phi) && phi.Sources.Length == block.Predecessors.Count
                && phi.Sources.All(v => expand(new Use(v, 64)) is Symbol { Kind: SymbolKind.Method, Value: MethodRef method }
                    && identity(call, pair.index, method)));
            if (!selected || call.Defines.Any(v => v is null)) continue;
            var results = call.Defines.Select(_ => new List<Variable>()).ToArray();
            for (var side = 0; side < block.Predecessors.Count; side++)
            {
                Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use && phis.TryGetValue(use.Variable, out var phi)
                    ? new Use(phi.Sources[side], use.Width) : null);
                var definitions = call.Defines.Select((v, i) =>
                {
                    var result = v with { Version = versions[v.Storage]++ };
                    results[i].Add(result);
                    return result;
                }).ToArray();
                var parent = block.Predecessors[side];
                var position = parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump ? 1 : 0);
                parent.Statements.Insert(position, call with { Arguments = call.Arguments.Select(OnEdge).ToArray(), Defines = definitions });
            }
            block.Statements.Remove(call);
            for (var i = 0; i < call.Defines.Length; i++)
                block.Statements.Insert(0, new Phi(call.Address, call.Defines[i], results[i].ToArray()));
            changed = true;
        }
        return changed;
    }

    internal static bool Split(MachineFunction function, Func<Call, bool> constructor, Func<Expr, Expr> expand)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        var changed = false;
        foreach (var block in function.Blocks)
        {
            var phis = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            var first = block.Statements.FindIndex(s => s is not (Phi or Nop));
            var allocation = first >= 0 && block.Statements[first] is Call { Op.Kind: OpKind.NewObject, Defines: [var created] } candidate ? candidate : null;
            var position = first + (allocation is null ? 0 : 1);
            if (position < 0 || position >= block.Statements.Count || block.Statements[position] is not Call call || !constructor(call)
                || call.Arguments.Length < 3 || call.Arguments[2] is not Use identity || !phis.TryGetValue(identity.Variable, out var method)
                || block.IsLandingPad || block.Predecessors.Count != 2 || block.Predecessors.Any(p => p.Handler is not null
                    || p.NormalSuccessors.ToArray() is not [var next] || next != block || p.Predecessors.Count != 1)
                || method.Sources.Any(v => expand(new Use(v, 64)) is not Symbol { Kind: SymbolKind.Method, Value: MethodRef })) continue;
            if (allocation is not null && call.Arguments[0] != new Use(allocation.Defines[0], 64)) continue;
            var results = call.Defines.Where(v => v is not null).ToHashSet();
            if (function.Blocks.SelectMany(b => b.Statements).Any(s => s is Phi phi && phi.Sources.Any(results.Contains)
                || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => results.Contains(u.Variable)))) continue;
            var allocated = new List<Variable>();
            var version = allocation is null ? 0 : function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
            {
                Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines, _ => [],
            }).Where(v => v.Storage == allocation.Defines[0].Storage).Max(v => v.Version) + 1;
            for (var side = 0; side < block.Predecessors.Count; side++)
            {
                Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use && phis.TryGetValue(use.Variable, out var phi)
                    ? new Use(phi.Sources[side], use.Width)
                    : e is Use original && allocation is not null && original.Variable == allocation.Defines[0] ? new Use(allocated[side], original.Width) : null);
                var parent = block.Predecessors[side];
                var index = parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump ? 1 : 0);
                if (allocation is not null)
                {
                    allocated.Add(allocation.Defines[0] with { Version = version + side });
                    parent.Statements.Insert(index++, allocation with { Arguments = allocation.Arguments.Select(OnEdge).ToArray(), Defines = [allocated[side]] });
                }
                parent.Statements.Insert(index, call with { Arguments = call.Arguments.Select(OnEdge).ToArray(), Defines = [], Results = [] });
            }
            block.Statements.Remove(call);
            if (allocation is not null)
            {
                block.Statements.Remove(allocation);
                block.Statements.Insert(0, new Phi(allocation.Address, allocation.Defines[0], allocated.ToArray()));
            }
            changed = true;
        }
        return changed;
    }
}
