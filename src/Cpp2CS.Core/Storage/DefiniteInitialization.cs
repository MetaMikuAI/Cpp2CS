using Cpp2CS.Recovery;

namespace Cpp2CS.Memory;

/// <summary>帧叶子的必定初始化分析；根与叶子由调用方的布局证据给出。</summary>
internal static class DefiniteInitialization
{
    internal static IEnumerable<ulong> Uninitialized(ManagedBody body, IReadOnlySet<ManagedValue> all,
        Func<ManagedValue, HashSet<ManagedValue>> Under)
    {
        IEnumerable<ManagedValue> Reads(ManagedValue value)
        {
            if (Under(value) is { Count: > 0 } own) return own;
            return ManagedValues.Children(value).SelectMany(Reads);
        }
        IEnumerable<ulong> Successors(ManagedBlock block) => block.Statements.LastOrDefault() is { } last ? ManagedValues.Edges(last).Select(e => e.Target) : [];
        var predecessors = body.Blocks.SelectMany(b => Successors(b).Select(s => (From: b.Address, To: s))).ToLookup(e => e.To, e => e.From);
        // handler 的首次到达来自异常边；普通回边的定义不能证明首次进入的初值。
        // catch/fault 入口取它所保护的各 try 块入口状态的交集：块内的定义只增不减，块入口的状态是块内任一抛出点状态的子集。
        var handlers = body.Regions.GroupBy(r => r.HandlerEntry).ToDictionary(g => g.Key, g => g.SelectMany(r => r.Try).Distinct().ToArray());
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var outputs = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ManagedValue>(all));
        HashSet<ManagedValue> Input(ManagedBlock b) => Entry(b, 0);
        HashSet<ManagedValue> Entry(ManagedBlock b, int depth)
        {
            if (b.Address == body.Blocks[0].Address) return [];
            if (handlers.TryGetValue(b.Address, out var tries))
            {
                if (depth > 4 || tries.Length == 0) return [];
                HashSet<ManagedValue>? merged = null;
                foreach (var t in tries.Where(blocks.ContainsKey))
                {
                    var tried = Entry(blocks[t], depth + 1);
                    if (merged is null) merged = tried; else merged.IntersectWith(tried);
                }
                return merged ?? [];
            }
            var parents = predecessors[b.Address].Where(outputs.ContainsKey).ToArray();
            if (parents.Length == 0) return [];
            var state = new HashSet<ManagedValue>(outputs[parents[0]]);
            foreach (var parent in parents.Skip(1)) state.IntersectWith(outputs[parent]);
            return state;
        }
        void Apply(HashSet<ManagedValue> state, ManagedStatement s)
        {
            if (s is ManagedStore store) state.UnionWith(Under(store.Target));
            if (s is ManagedAssignment assignment) state.UnionWith(Under(assignment.Target));
            if (s is ManagedCall { Result: { } result }) state.UnionWith(Under(result));
        }
        bool changed;
        do
        {
            changed = false;
            foreach (var block in body.Blocks)
            {
                var state = Input(block);
                foreach (var statement in block.Statements) Apply(state, statement);
                if (!state.SetEquals(outputs[block.Address])) { outputs[block.Address] = state; changed = true; }
            }
        } while (changed);
        foreach (var block in body.Blocks)
        {
            var state = Input(block);
            foreach (var statement in block.Statements)
            {
                var operands = statement switch
                {
                    ManagedStore s => new[] { s.Value },
                    ManagedAssignment a => new[] { a.Value },
                    _ => ManagedValues.Of(statement),
                };
                operands = operands.Concat(ManagedValues.CopiedValues(statement));
                if (operands.SelectMany(Reads).Any(r => !state.Contains(r)))
                    yield return statement.Address;
                Apply(state, statement);
            }
        }
    }
}
