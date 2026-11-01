using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ReachingAtPass
{
    internal static Variable? ReachingAt(this IdiomState state, Block block, Storage storage, Dictionary<Block, Variable?> memo) => state.Reaching(block, storage, memo, [], out _) is var (v, known) && known ? v : null;
}
