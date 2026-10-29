using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static partial class CallIdentityChoices
{
    // 地址随分支变化的共享写入回到各入边；静态字段与实例字段不再混成未知指针。
    internal static bool SplitStores(MachineFunction function)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.IsLandingPad || block.Predecessors.Count is < 2 or > 4 || block.Predecessors.Any(p => p == block || p.Handler is not null
                || p.NormalSuccessors.ToArray() is not [var next] || next != block)) continue;
            if (block.Statements.FirstOrDefault(s => s is not (Phi or Nop)) is not Store store) continue;
            var phis = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            if (phis.Values.Any(p => p.Sources.Length != block.Predecessors.Count)
                || !ExprMap.Walk(store.Target).OfType<Use>().Any(u => phis.ContainsKey(u.Variable))) continue;
            for (var side = 0; side < block.Predecessors.Count; side++)
            {
                Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use && phis.TryGetValue(use.Variable, out var phi)
                    ? new Use(phi.Sources[side], use.Width) : null);
                var parent = block.Predecessors[side];
                var position = parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump ? 1 : 0);
                parent.Statements.Insert(position, ExprMap.MapOperands(store, OnEdge));
            }
            block.Statements.Remove(store);
            changed = true;
        }
        return changed;
    }
}
