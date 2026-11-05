using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class EqualAddressPhisPass
{
    internal static bool EqualAddressPhis(this IdiomState state)
    {
        var changed = false;
        var phis = state.All.OfType<Phi>().ToDictionary(p => p.Target);
        void Leaves(Expr value, HashSet<Variable> active, HashSet<Expr> leaves)
        {
            value = state.defs.Expand(value);
            if (value is Use use && phis.TryGetValue(use.Variable, out var phi))
            {
                if (!active.Add(use.Variable))
                    return;
                foreach (var source in phi.Sources)
                    Leaves(new Use(source, source.Width), active, leaves);
            }
            else
                leaves.Add(value);
        }

        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Phi phi || phi.Sources.Length == 0)
                    continue;
                var leaves = new HashSet<Expr>();
                Leaves(new Use(phi.Target, phi.Target.Width), [], leaves);
                var sources = leaves.ToArray();
                // 元数据实体是不可变的常量：初始化守卫两臂各读一次 RGCTX 表后合流，也是同一个值。
                if (sources is not [var address and (Symbol or Binary { Op: BinOp.Add, Right: Const })] || ExprMap.Walk(address).Any(e => e is Load or Unknown or Intrinsic))
                    continue;
                block.Statements[i] = new Define(phi.Address, phi.Target, address);
                changed = true;
            }

        return changed;
    }
}
