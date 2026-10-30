using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Idioms;

internal static class RemovePass
{
    internal static void Remove(this IdiomState state, IEnumerable<Block> blocks) => state.removed.UnionWith(blocks);
}
