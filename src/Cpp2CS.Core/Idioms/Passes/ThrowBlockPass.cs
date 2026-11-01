using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ThrowBlockPass
{
    internal static RuntimeHelper? ThrowBlock(this IdiomState state, Block block)
    {
        if (block.NormalSuccessors.Any() || block.Statements.Count == 0 || block.Statements[^1] is not Call call)
            return null;
        if (state.owner.HelperOf(call) is not { Kind: HelperKind.Throw } helper)
            return null;
        return block.Statements.Take(block.Statements.Count - 1).All(s => s is Phi or Nop or Define { Value: Const }) ? helper : null;
    }
}
