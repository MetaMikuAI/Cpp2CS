using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomState;

namespace Cpp2CS.Idioms;

internal static class ReachingBeforePass
{
    internal static Variable? ReachingBefore(this IdiomState state, Block head, Point start, Storage storage) => state.LastDefinition(head, storage, start.Index, start.Address) ?? state.ReachingAt(head, storage, new());
}
