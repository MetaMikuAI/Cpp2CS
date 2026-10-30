using System.Reflection;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>精确类指针检查成功后，细化同一 SSA 引用与后续拆箱的类型。</summary>
internal static class CheckedClassValues
{
    public static bool Run(MachineFunction function, Func<Use, Expr?> definition, Func<Variable> fresh)
    {
        var dominators = Dominators.Compute(function);
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne } compare } branch)
                continue;
            var (left, right) = compare.Left is Symbol ? (compare.Right, compare.Left) : (compare.Left, compare.Right);
            if (left is not Use klass || right is not Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsValueType: true } type }
                || type.Definition.FullName == "System.Nullable" || definition(klass) is not Load { Width: 64, Address: Use value })
                continue;
            var success = block.NormalSuccessors.SingleOrDefault(b => b.Start == (compare.Cond == Cond.Eq ? branch.Target : branch.Fallthrough));
            if (success is null || success.Predecessors.Count != 1) continue;
            for (var index = 0; index < success.Statements.Count; index++)
                if (success.Statements[index] is Call { Op: { Kind: OpKind.Unbox, Operand: null } op, Arguments: [var obj, ..] } unbox && obj == value)
                {
                    success.Statements[index] = unbox with { Op = op with { Operand = type } };
                    changed = true;
                }
        }
        foreach (var block in function.Blocks)
            for (var index = 0; index < block.Statements.Count; index++)
            {
                if (block.Statements[index] is not Call
                    {
                        Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException",
                        Arguments: [Compare
                        {
                            Cond: Cond.Ne, Left: Use klass, Right: Symbol
                            {
                                Kind: SymbolKind.Class,
                                Value: DefinitionRef { Definition.IsValueType: false } type
                            }
                        }]
                    } check
                    || (type.Definition.Attributes & TypeAttributes.Sealed) == 0
                    || definition(klass) is not Load { Width: 64, Address: Use { Width: 64 } value }) continue;
                var cast = fresh();
                if (!Refine(function, block, index + 1, value, cast, dominators)) continue;
                block.Statements.Insert(++index, new Call(check.Address, CallKind.Direct, Expr.C(0, 64))
                {
                    Op = new RuntimeOp(OpKind.IsInst, type),
                    Arguments = [value],
                    Results = [cast.Storage],
                    Defines = [cast],
                });
                changed = true;
            }
        return changed;
    }

    internal static bool Refine(MachineFunction function, Block start, int position, Use value, Variable cast, Dominators dominators)
    {
        var changed = false;
        foreach (var block in function.Blocks)
            for (var index = 0; index < block.Statements.Count; index++)
            {
                if (block.Statements[index] is Phi phi)
                {
                    var sources = phi.Sources.Select((source, edge) => source == value.Variable
                        && dominators.Dominates(start.Index, block.Predecessors[edge].Index) ? cast : source).ToArray();
                    changed |= !sources.SequenceEqual(phi.Sources);
                    block.Statements[index] = phi with { Sources = sources };
                }
                else if (dominators.Dominates(start.Index, block.Index) && (block != start || index >= position))
                    block.Statements[index] = ExprMap.MapOperands(block.Statements[index], expression => ExprMap.Map(expression,
                        part =>
                        {
                            if (part is not Use use || use.Variable != value.Variable) return null;
                            changed = true;
                            return new Use(cast, use.Width);
                        }));
            }
        return changed;
    }
}
