using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class DynamicArrayElementChecksPass
{
    internal static bool DynamicArrayElementChecks(this IdiomState state)
    {
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call { Op: { Kind: OpKind.IsInst, Operand: null }, Arguments: [var value, var type] } call && (state.RawDefinition(type) ?? type) is Load { Width: 64, Address: var elementAddress } && SplitPass.Split(elementAddress) is (Use klass, RuntimeLayout.ClassElementClass) && state.RawDefinition(klass) is Load { Width: 64, Address: Use array })
                {
                    block.Statements[i] = call with
                    {
                        Op = new RuntimeOp(OpKind.IsInstArrayElement, null),
                        Arguments = [value, array]
                    };
                    changed = true;
                }

        return changed;
    }
}
