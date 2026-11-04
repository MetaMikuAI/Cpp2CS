using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Flow;

/// <summary>同一循环回边上的常步长计数器等于初值加步长乘以单位计数器，运算均模 2^64。</summary>
internal static class AffineInduction
{
    internal static bool Run(MachineFunction function, Func<Expr, Expr?> definition)
    {
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.Predecessors.Count != 2) continue;
            var phis = block.Statements.OfType<Phi>().Where(p => p.Sources.Length == 2).ToArray();
            for (var seed = 0; seed < 2; seed++)
            {
                var index = InductionVariables.UnitCounter(block, seed, 64, definition);
                if (index is null) continue;
                foreach (var phi in phis)
                {
                    if (phi == index || InductionVariables.Read(block, phi, seed, definition) is not
                        { Initial: Const initial, Width: 64, Step: not (0 or 1) } induction) continue;
                    var (start, step) = (initial.Value, induction.Step);
                    var expression = Fold.Binary(BinOp.Add, Expr.C(start, 64),
                        Fold.Binary(BinOp.Mul, new Use(index.Target, 64), Expr.C(step, 64), 64), 64);
                    block.Statements.Remove(phi);
                    var position = block.Statements.TakeWhile(s => s is Phi).Count();
                    block.Statements.Insert(position, new Define(phi.Address, phi.Target, expression));
                    changed = true;
                }
            }
        }
        return changed;
    }
}
