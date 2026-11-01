using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ZeroUnionConditionsPass
{
    internal static bool ZeroUnionConditions(this IdiomState state)
    {
        var changed = false;
        Expr? Rewrite(Expr expression)
        {
            if (expression is not Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } test)
                return null;
            var left = test.Left;
            var seen = new HashSet<Variable>();
            while (left is Use use && seen.Count < 16 && seen.Add(use.Variable)
                && state.RawDefinition(use) is (Use or Binary { Op: BinOp.Or }) and var source && source.Width == use.Width)
                left = source;
            if (left is not Binary { Op: BinOp.Or }) return null;
            var folded = Fold.Compare(test.Cond, left, test.Right);
            if (folded is not Logical) return null;
            changed = true;
            return folded;
        }
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Rewrite));
        return changed;
    }
}
