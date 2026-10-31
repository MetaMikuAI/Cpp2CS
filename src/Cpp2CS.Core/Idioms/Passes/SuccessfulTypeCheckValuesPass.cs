using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class SuccessfulTypeCheckValuesPass
{
    internal static bool SuccessfulTypeCheckValues(this IdiomState state) => Run(state.function, state.RawDefinition, state.Fresh);

    internal static bool Run(MachineFunction function, Func<Use, Expr?> definitionOf, Func<Variable> fresh)
    {
        var dominators = Dominators.Compute(function);
        var checks = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Op?.Kind == OpKind.TypeCheck).ToArray();
        var changed = false;
        foreach (var check in checks)
        {
            if (check.Op?.Operand is not TypeRef type || check.Arguments is not [Use klass] || definitionOf(klass) is not Load { Width: 64, Address: Use obj } || check.Defines.FirstOrDefault() is not { } flag)
                continue;
            bool Flag(Expr value, int depth = 0) => depth < 12 && value switch
            {
                Use u when u.Variable == flag => true,
                Use u when definitionOf(u) is { } definition => Flag(definition, depth + 1),
                Ir.Convert { Kind: ConvKind.Truncate or ConvKind.ZeroExtend or ConvKind.SignExtend } c => Flag(c.Operand, depth + 1),
                Binary { Op: BinOp.And, Right: Const { Value: 1 } } b => Flag(b.Left, depth + 1),
                _ => false,
            };
            foreach (var block in function.Blocks)
            {
                for (var index = 0; index < block.Statements.Count; index++)
                    if (type is DefinitionRef { Definition.IsValueType: false }
                        && block.Statements[index] is Define { Value: Select select } definition
                        && Fold.Simplify(select.Condition) is Compare { Cond: Cond.Eq or Cond.Ne, Left: var tested, Right: Const { Value: 0 } } comparison
                        && Flag(tested)
                        && (comparison.Cond == Cond.Ne ? select.True : select.False) == obj
                        && (comparison.Cond == Cond.Ne ? select.False : select.True) is Const { Value: 0 })
                    {
                        block.Statements[index] = new Call(definition.Address, CallKind.Direct, Expr.C(0, 64))
                        {
                            Op = new(OpKind.IsInst, type), Arguments = [obj],
                            Results = [definition.Target.Storage], Defines = [definition.Target],
                        };
                        changed = true;
                    }
            }
            foreach (var block in function.Blocks.ToArray())
            {
                var at = block.Statements.FindIndex(s => s is Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Eq, Left: var result, Right: Const { Value: 0 } }] } && Flag(result));
                Block? start = at >= 0 ? block : null;
                var position = at + 1;
                if (start is null && block.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: var result, Right: Const { Value: 0 } } test } branch && Flag(result))
                {
                    var address = test.Cond == Cond.Eq ? branch.Fallthrough : branch.Target;
                    start = CheckedClassValues.SuccessEdge(function, block, branch, address, obj);
                    if (start is not null) dominators = Dominators.Compute(function);
                    position = start?.Statements.TakeWhile(s => s is Phi).Count() ?? 0;
                }

                if (start is null)
                    continue;
                var cast = fresh();
                CheckedClassValues.Refine(function, start, position, obj, cast, dominators);
                start.Statements.Insert(position, new Call(check.Address, CallKind.Direct, Expr.C(0, 64)) { Op = new RuntimeOp(OpKind.IsInst, type), Arguments = [obj], Results = [cast.Storage], Defines = [cast], });
                changed = true;
                break;
            }
        }

        return changed;
    }
}
