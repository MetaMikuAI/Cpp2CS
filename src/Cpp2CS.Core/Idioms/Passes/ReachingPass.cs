using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ReachingPass
{
    internal static (Variable? Value, bool Known) Reaching(this IdiomState state, Block block, Storage storage, Dictionary<Block, Variable?> memo, HashSet<Block> active, out bool assumed)
    {
        assumed = false;
        foreach (var phi in block.Statements.OfType<Phi>())
            if (phi.Target.Storage == storage)
                return (phi.Target, true);
        // 已折叠、等待 Cleanup 删除的区域块不再是路径
        var predecessors = block.Predecessors.Distinct().Where(p => !state.removed.Contains(p)).ToArray();
        if (predecessors.Length == 0)
            return block == state.function.EntryBlock ? (new Variable(storage, 0), true) : (null, false);
        if (memo.TryGetValue(block, out var cached))
            return (cached, cached is not null);
        if (active.Contains(block))
        {
            assumed = true;
            return (null, true);
        }

        if (active.Count > 400)
            return (null, false);
        active.Add(block);
        Variable? found = null;
        var known = true;
        foreach (var predecessor in predecessors)
        {
            var v = state.LastDefinition(predecessor, storage, predecessor.Statements.Count, ulong.MaxValue);
            if (v is null)
            {
                (v, var ok) = state.Reaching(predecessor, storage, memo, active, out var inner);
                assumed |= inner;
                if (!ok)
                {
                    known = false;
                    break;
                }

                if (v is null)
                    continue; // 回边：不提供信息
            }

            if (found is not null && v != found)
            {
                known = false;
                break;
            }

            found = v;
        }

        active.Remove(block);
        if (!known || found is null)
        {
            if (!assumed || !known)
                memo[block] = null;
            return (null, false);
        }

        if (!assumed)
            memo[block] = found;
        return (found, true);
    }
}
