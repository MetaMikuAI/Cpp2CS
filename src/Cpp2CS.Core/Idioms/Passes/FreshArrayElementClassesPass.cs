using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class FreshArrayElementClassesPass
{
    internal static bool FreshArrayElementClasses(this IdiomState state)
    {
        var arrays = state.function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Op is { Kind: OpKind.NewArray, Operand: ArrayRef } && c.Defines.Length > 0).ToDictionary(c => c.Defines[0], c => (ArrayRef)c.Op!.Operand!);
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: { Kind: OpKind.IsInst, Operand: null } op, Arguments: [var value, var type] } call || state.defs.Expand(type) is not Load { Width: 64, Address: var elementAddress } || SplitPass.Split(elementAddress) is not (Load { Width: 64, Address: Use { Variable: var array } }, RuntimeLayout.ClassElementClass) || !arrays.TryGetValue(array, out var arrayType))
                    continue;
                block.Statements[i] = call with
                {
                    Op = op with
                    {
                        Operand = arrayType.Element
                    },
                    Arguments = [value, new Symbol(SymbolKind.Class, arrayType.Element)]
                };
                changed = true;
            }

        return changed;
    }
}
