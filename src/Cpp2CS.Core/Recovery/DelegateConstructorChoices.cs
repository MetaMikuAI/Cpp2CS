using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>分支选择方法和接收者后共用的委托构造，沿原入边还原成各分支的构造。</summary>
internal static class DelegateConstructorChoices
{
    internal static bool Split(MachineFunction function, Func<Call, bool> constructor, Func<Expr, Expr> expand)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        var changed = false;
        foreach (var block in function.Blocks)
        {
            var phis = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            if (block.Statements.FirstOrDefault(s => s is not (Phi or Nop)) is not Call call || !constructor(call)
                || call.Arguments.Length < 3 || call.Arguments[2] is not Use identity || !phis.TryGetValue(identity.Variable, out var method)
                || block.IsLandingPad || block.Predecessors.Count != 2 || block.Predecessors.Any(p => p.Handler is not null
                    || p.NormalSuccessors.ToArray() is not [var next] || next != block || p.Predecessors.Count != 1)
                || method.Sources.Any(v => expand(new Use(v, 64)) is not Symbol { Kind: SymbolKind.Method, Value: MethodRef })) continue;
            var results = call.Defines.Where(v => v is not null).ToHashSet();
            if (function.Blocks.SelectMany(b => b.Statements).Any(s => s is Phi phi && phi.Sources.Any(results.Contains)
                || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => results.Contains(u.Variable)))) continue;
            for (var side = 0; side < block.Predecessors.Count; side++)
            {
                Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use && phis.TryGetValue(use.Variable, out var phi)
                    ? new Use(phi.Sources[side], use.Width) : null);
                var parent = block.Predecessors[side];
                var index = parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump ? 1 : 0);
                parent.Statements.Insert(index, call with { Arguments = call.Arguments.Select(OnEdge).ToArray(), Defines = [], Results = [] });
            }
            block.Statements.Remove(call);
            changed = true;
        }
        return changed;
    }
}
