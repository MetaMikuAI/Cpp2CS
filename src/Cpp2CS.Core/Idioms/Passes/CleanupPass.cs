using Cpp2CS.Machine.Ssa;
using static Cpp2CS.Idioms.IdiomRewriter;

namespace Cpp2CS.Idioms;

internal static class CleanupPass
{
    internal static void Cleanup(this IdiomState state)
    {
        state.Result.Errors.AddRange(Lowering.Cleanup(state.function));
        state.removed.Clear();
        state.defs = new Defs(state.function);
    }
}
