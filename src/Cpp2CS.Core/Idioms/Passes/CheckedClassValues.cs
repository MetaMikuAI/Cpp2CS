using System.Reflection;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>精确类指针检查成功后，同一 SSA 引用可按已检查的封闭引用类型使用。</summary>
internal static class CheckedClassValues
{
    public static bool Run(MachineFunction function, Func<Use, Expr?> definition, Func<Variable> fresh)
    {
        var dominators = Dominators.Compute(function);
        var changed = false;
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
