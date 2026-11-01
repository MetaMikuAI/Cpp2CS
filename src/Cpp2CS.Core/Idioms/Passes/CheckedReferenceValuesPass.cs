using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class CheckedReferenceValuesPass
{
    internal static bool CheckedReferenceValues(this IdiomState state)
    {
        var dominators = Dominators.Compute(state.function);
        var changed = false;
        foreach (var join in state.function.Blocks.Where(b => b.Predecessors.Count == 2))
            foreach (var check in join.Predecessors)
            {
                if (check.Statements.LastOrDefault() is not Jump to || to.Target != join.Start)
                    continue;
                var path = new List<Block>
                {
                    check
                };
                var first = check;
                while (first.Predecessors is [var parent] && parent.Statements.LastOrDefault() is Jump next && next.Target == first.Start && !path.Contains(parent))
                {
                    path.Add(parent);
                    first = parent;
                }

                if (first.Predecessors is not [var head] || !join.Predecessors.Contains(head) || head.Statements.LastOrDefault() is not Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use obj, Right: Const { Value: 0 } } test } branch || (test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough) != join.Start)
                    continue;
                var calls = path.SelectMany(b => b.Statements).OfType<Call>().ToArray();
                TypeRef? target = null;
                foreach (var call in calls)
                {
                    if (call is { Op.Kind: OpKind.TypeCheck, Op.Operand: DefinitionRef { Definition.IsValueType: false } type, Arguments: [Use klass] } && state.RawDefinition(klass) is Load { Width: 64, Address: var source } && source == obj && call.Defines.FirstOrDefault() is { } flag && calls.Any(c => c is { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Eq, Left: Use result, Right: Const { Value: 0 } }] } && result.Variable == flag))
                        target = type;
                    if (call is { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ne, Left: Use sealedClass, Right: Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsValueType: false } sealedType } }] } && (sealedType.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) != 0 && state.RawDefinition(sealedClass) is Load { Width: 64, Address: var instance } && instance == obj)
                        target = sealedType;
                }

                if (target is null)
                    continue;
                var cast = state.Fresh();
                state.RefineReferenceUses(join, 0, obj, cast, dominators);
                join.Statements.Insert(join.Statements.TakeWhile(s => s is Phi).Count(), new Call(join.Start, CallKind.Direct, Expr.C(0, 64)) { Op = new RuntimeOp(OpKind.IsInst, target), Arguments = [obj], Results = [cast.Storage], Defines = [cast], });
                changed = true;
                break;
            }

        return changed;
    }
}
