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
        foreach (var block in function.Blocks.ToArray())
        {
            if (block.Statements.LastOrDefault() is not Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne } compare } branch)
                continue;
            var (left, right) = compare.Left is Symbol ? (compare.Right, compare.Left) : (compare.Left, compare.Right);
            if (left is not Use klass || right is not Symbol { Kind: SymbolKind.Class, Value: DefinitionRef type }
                || type.Definition.FullName == "System.Nullable" || definition(klass) is not Load { Width: 64, Address: Use value })
                continue;
            var success = block.NormalSuccessors.SingleOrDefault(b => b.Start == (compare.Cond == Cond.Eq ? branch.Target : branch.Fallthrough));
            if (success is null) continue;
            if (!type.Definition.IsValueType)
            {
                success = SuccessEdge(function, block, branch, success.Start, value);
                if (success is null) continue;
                dominators = Dominators.Compute(function);
                var position = success.Statements.TakeWhile(s => s is Phi).Count();
                var cast = fresh();
                if (!Refine(function, success, position, value, cast, dominators)) continue;
                success.Statements.Insert(position, new Call(branch.Address, CallKind.Direct, Expr.C(0, 64))
                {
                    Op = new RuntimeOp(OpKind.IsInst, type), Arguments = [value], Results = [cast.Storage], Defines = [cast],
                });
                changed = true;
                continue;
            }
            if (success.Predecessors.Count != 1) continue;
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

    // 成功边直接进入合流时，转换只作用于该入边，不能覆盖其他来源。
    internal static Block? SuccessEdge(MachineFunction function, Block parent, Branch branch, ulong address, Use value)
    {
        var target = parent.NormalSuccessors.FirstOrDefault(b => b.Start == address);
        if (target is null || target.Predecessors.Count == 1) return target;
        if (function.Range.ExceptionRegions.Length != 0 || parent.Handler is not null || target.IsLandingPad
            || branch.Target == branch.Fallthrough || target.Predecessors.Count(p => p == parent) != 1
            || parent.Successors.Count(b => b == target) != 1) return null;
        var side = target.Predecessors.IndexOf(parent);
        if (!target.Statements.OfType<Phi>().Any(p => p.Sources.Length == target.Predecessors.Count && p.Sources[side] == value.Variable)) return null;
        var label = Math.Max(NameSupply.JoinedEdgeBase, function.Blocks.Max(b => b.Start) + 1);
        var edge = new Block(label) { End = label + 1, Statements = [new Jump(branch.Address, target.Start)] };
        edge.Predecessors.Add(parent);
        edge.Successors.Add(target);
        parent.Successors[parent.Successors.IndexOf(target)] = edge;
        target.Predecessors[side] = edge;
        parent.Statements[^1] = branch with
        {
            Target = branch.Target == address ? label : branch.Target,
            Fallthrough = branch.Fallthrough == address ? label : branch.Fallthrough,
        };
        function.Blocks.Add(edge);
        function.Renumber();
        return edge;
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
