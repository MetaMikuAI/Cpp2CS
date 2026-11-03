using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Idioms;

/// <summary>同一循环回边上的常步长计数器等于初值加步长乘以单位计数器，运算均模 2^64。</summary>
internal static class AffineInductionPass
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
                bool Initial(Phi phi, out ulong value)
                {
                    value = 0;
                    if (definition(new Use(phi.Sources[seed], 64)) is not Const { Width: 64 } constant) return false;
                    value = constant.Value;
                    return true;
                }
                bool Step(Phi phi, out ulong value)
                {
                    value = 0;
                    if (definition(new Use(phi.Sources[1 - seed], 64)) is not Binary
                        { Op: BinOp.Add, Width: 64, Left: Use previous, Right: Const step } || previous.Variable != phi.Target) return false;
                    value = step.Value;
                    return true;
                }
                var index = phis.FirstOrDefault(p => Initial(p, out var start) && start == 0 && Step(p, out var step) && step == 1);
                if (index is null) continue;
                foreach (var phi in phis)
                {
                    if (phi == index || !Initial(phi, out var start) || !Step(phi, out var step) || step is 0 or 1) continue;
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
