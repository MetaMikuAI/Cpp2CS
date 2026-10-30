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
                var following = block.Statements.Skip(i + 1).Where(s => s is not (Nop or Jump)).ToArray();
                if (following.Length == 0 && block.NormalSuccessors.ToArray() is [var next] && next.Predecessors.Count == 1)
                    following = next.Statements.Where(s => s is not Nop).ToArray();
                if (following.FirstOrDefault() is not Call { Op.Kind: OpKind.Unbox, Arguments: [var value, ..] } unbox || !Equals(unbox.Op.Operand, type) || !Equals(state.defs.Expand(value), obj))
                    continue;
                // unbox 在同一位置执行类型与 null 检查，原生 element_class 检查不另造托管字段访问。
                block.Statements[i] = new Nop(check.Address, "拆箱类型检查");
                changed = true;
            }

        return changed;
    }
}
