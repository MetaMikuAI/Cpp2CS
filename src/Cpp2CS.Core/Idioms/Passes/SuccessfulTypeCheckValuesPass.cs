using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class SuccessfulTypeCheckValuesPass
{
    internal static bool SuccessfulTypeCheckValues(this IdiomState state)
    {
        var dominators = Dominators.Compute(state.function);
        var checks = state.All.OfType<Call>().Where(c => c.Op?.Kind == OpKind.TypeCheck).ToArray();
        var changed = false;
        foreach (var check in checks)
        {
            if (check.Op?.Operand is not TypeRef type || check.Arguments is not [Use klass] || state.RawDefinition(klass) is not Load { Width: 64, Address: Use obj } || check.Defines.FirstOrDefault() is not { } flag)
                continue;
            foreach (var block in state.function.Blocks)
            {
                var at = block.Statements.FindIndex(s => s is Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Eq, Left: Use result, Right: Const { Value: 0 } }] } && result.Variable == flag);
                Block? start = at >= 0 ? block : null;
                var position = at + 1;
                if (start is null && block.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use result, Right: Const { Value: 0 } } test } branch && result.Variable == flag)
                {
                    var address = test.Cond == Cond.Eq ? branch.Fallthrough : branch.Target;
                    start = block.NormalSuccessors.FirstOrDefault(b => b.Start == address && b.Predecessors.Count == 1);
                    position = start?.Statements.TakeWhile(s => s is Phi).Count() ?? 0;
                }

                if (start is null)
                    continue;
                var cast = state.Fresh();
                state.RefineReferenceUses(start, position, obj, cast, dominators);
                start.Statements.Insert(position, new Call(check.Address, CallKind.Direct, Expr.C(0, 64)) { Op = new RuntimeOp(OpKind.IsInst, type), Arguments = [obj], Results = [cast.Storage], Defines = [cast], });
                changed = true;
                break;
            }
        }

        return changed;
    }
}
