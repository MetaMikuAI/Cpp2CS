using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class UnboxGuardsPass
{
    internal static bool UnboxGuards(this IdiomState state)
    {
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ne } compare] } check || state.defs.Expand(compare.Left) is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Load { Width: 64, Address: var obj }, Right: Const { Value: RuntimeLayout.ClassElementClass } } } || state.defs.Expand(compare.Right) is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type }, Right: Const { Value: RuntimeLayout.ClassElementClass } } })
                    continue;
                var targetBlock = block;
                var following = block.Statements.Skip(i + 1).Where(s => s is not (Nop or Jump)).ToArray();
                if (following.Length == 0 && block.NormalSuccessors.ToArray() is [var next] && next.Predecessors.Count == 1)
                {
                    targetBlock = next;
                    following = next.Statements.Where(s => s is not Nop).ToArray();
                }
                var first = following.FirstOrDefault();
                if (first is Call { Op.Kind: OpKind.Unbox, Arguments: [var value, ..] } unbox && Equals(unbox.Op.Operand, type) && Equals(state.defs.Expand(value), obj))
                {
                    // unbox 后的元素类检查是冗余的：isinst 已确认类型，空值路径也不会到达这里
                    block.Statements[i] = new Nop(check.Address, "内联 unbox 空检查");
                    changed = true;
                    continue;
                }
                // 内联 unbox.any 不调用 helper：检查之后直接从对象数据区读取值类型。
                var load = first is Define { Value: Load direct } ? direct
                    : first is Define { Value: Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: Load converted } } ? converted : null;
                if (type is not DefinitionRef { Definition.IsValueType: true }) continue;
                if (first is Define data && load is { Width: 32 or 64, Address: Binary { Op: BinOp.Add, Left: var source, Right: Const { Value: RuntimeLayout.ObjectHeaderSize } } }
                    && Equals(state.defs.Expand(source), obj))
                {
                    var at = targetBlock.Statements.FindIndex(s => ReferenceEquals(s, first));
                    if (at < 0) continue;
                    targetBlock.Statements[at] = new Call(data.Address, CallKind.Direct, Expr.C(0, 64))
                    {
                        Op = new RuntimeOp(OpKind.UnboxAny, type),
                        Arguments = [source],
                        Results = [data.Target.Storage],
                        Defines = [data.Target],
                    };
                }
                else
                {
                    // 值没有被使用：仍保留 unbox.any 的异常语义，结果在写出时作为未使用的局部丢弃。
                    var result = state.Fresh();
                    block.Statements[i] = new Nop(check.Address, "内联 unbox 空检查");
                    block.Statements.Insert(i + 1, new Call(check.Address, CallKind.Direct, Expr.C(0, 64))
                    {
                        Op = new RuntimeOp(OpKind.UnboxAny, type),
                        Arguments = [obj],
                        Results = [result.Storage],
                        Defines = [result],
                    });
                    i++;
                    changed = true;
                    continue;
                }
                block.Statements[i] = new Nop(check.Address, "内联 unbox 空检查");
                changed = true;
            }

        return changed;
    }
}
