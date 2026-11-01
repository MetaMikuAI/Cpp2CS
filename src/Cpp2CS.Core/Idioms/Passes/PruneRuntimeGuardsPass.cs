using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class PruneRuntimeGuardsPass
{
    internal static void PruneRuntimeGuards(this IdiomState state)
    {
        foreach (var block in state.function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch { Condition: Const constant } branch)
                continue;
            var normal = block.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0].Start != branch.Target || normal[1].Start != branch.Fallthrough)
                continue;
            var side = constant.Value != 0 ? 0 : 1;
            block.Statements[^1] = new Jump(branch.Address, normal[side].Start);
            MachineFunction.RemoveEdgeAt(block, 1 - side);
        }

        state.Cleanup();
    }
}
