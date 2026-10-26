using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>传播有限的局部常量集合，并在条件边上缩小取值范围。</summary>
internal static class AsyncConstantBranches
{
    public static void Run(IReadOnlyDictionary<ulong, List<ManagedStatement>> blocks, ulong entry, IReadOnlyList<ManagedRegion> regions,
        Func<ManagedValue, Dictionary<Variable, ulong>, ulong?> evaluate)
    {
        var inputs = new Dictionary<ulong, Dictionary<Variable, HashSet<ulong>>> { [entry] = [] };
        var handlers = regions.SelectMany(r => r.Try.Select(a => (Address: a, r.HandlerEntry))).ToLookup(p => p.Address, p => p.HandlerEntry);
        var pending = new Queue<ulong>([entry]);
        static Dictionary<Variable, HashSet<ulong>> Clone(Dictionary<Variable, HashSet<ulong>> state) => state.ToDictionary(p => p.Key, p => new HashSet<ulong>(p.Value));
        List<(Dictionary<Variable, ulong> Inputs, ulong Value)>? Values(ManagedValue value, Dictionary<Variable, HashSet<ulong>> state)
        {
            var variables = ManagedValues.Walk(value).OfType<LocalValue>().Select(l => l.Variable).Distinct().ToArray();
            var choices = new List<Dictionary<Variable, ulong>> { new() };
            foreach (var variable in variables)
            {
                if (!state.TryGetValue(variable, out var values) || choices.Count * values.Count > 128) return null;
                choices = choices.SelectMany(c => values.Select(v => new Dictionary<Variable, ulong>(c) { [variable] = v })).ToList();
            }
            var results = new List<(Dictionary<Variable, ulong>, ulong)>();
            foreach (var choice in choices)
            {
                if (evaluate(value, choice) is not { } result) return null;
                results.Add((choice, result));
            }
            return results;
        }
        HashSet<ulong>? Constants(ManagedValue value, Dictionary<Variable, HashSet<ulong>> state) => Values(value, state) is { } values
            && values.Select(v => v.Value).Distinct().ToArray() is { Length: <= 8 } constants ? constants.ToHashSet() : null;
        static void Set(Dictionary<Variable, HashSet<ulong>> state, Variable variable, HashSet<ulong>? values)
        { if (values is null) state.Remove(variable); else state[variable] = values; }
        Dictionary<Variable, HashSet<ulong>> Transfer(ulong address)
        {
            var state = Clone(inputs[address]);
            foreach (var statement in blocks[address])
            {
                if (statement is ManagedAssignment assignment) Set(state, assignment.Target.Variable, Constants(assignment.Value, state));
                if (statement is ManagedCall { Result: { } result }) state.Remove(result.Variable);
                if (statement is ManagedAwait { Result: { } awaited }) state.Remove(awaited.Variable);
                foreach (var local in ManagedValues.Of(statement).SelectMany(ManagedValues.Walk).OfType<AddressValue>()
                    .Select(a => a.Target).OfType<LocalValue>()) state.Remove(local.Variable);
            }
            return state;
        }
        void Merge(ulong target, Dictionary<Variable, HashSet<ulong>> state)
        {
            if (!blocks.ContainsKey(target)) return;
            if (!inputs.TryGetValue(target, out var previous)) { inputs[target] = Clone(state); pending.Enqueue(target); return; }
            var changed = false;
            foreach (var variable in previous.Keys.ToArray())
            {
                if (!state.TryGetValue(variable, out var values)) { previous.Remove(variable); changed = true; continue; }
                var count = previous[variable].Count;
                previous[variable].UnionWith(values);
                if (previous[variable].Count > 8) { previous.Remove(variable); changed = true; }
                else changed |= count != previous[variable].Count;
            }
            if (changed) pending.Enqueue(target);
        }
        void Edge(ManagedEdge edge, Dictionary<Variable, HashSet<ulong>> state, ManagedValue? condition = null, bool taken = true)
        {
            var next = Clone(state);
            if (condition is not null && Values(condition, state) is { } possibilities)
            {
                var allowed = possibilities.Where(p => (p.Value != 0) == taken).ToArray();
                if (allowed.Length == 0) return;
                foreach (var variable in allowed[0].Inputs.Keys) next[variable] = allowed.Select(p => p.Inputs[variable]).ToHashSet();
            }
            var copies = edge.Copies.Select(c => (c.Target.Variable, Value: Constants(c.Value, next))).ToArray();
            foreach (var (variable, value) in copies) Set(next, variable, value);
            Merge(edge.Target, next);
        }
        while (pending.TryDequeue(out var address))
        {
            var state = Transfer(address);
            foreach (var handler in handlers[address]) Merge(handler, []);
            if (blocks[address].LastOrDefault() is ManagedBranch branch)
            { Edge(branch.Taken, state, branch.Condition); Edge(branch.Fallthrough, state, branch.Condition, false); }
            else foreach (var edge in blocks[address].SelectMany(ManagedValues.Edges)) Edge(edge, state);
        }
        foreach (var address in inputs.Keys)
            if (blocks[address].LastOrDefault() is ManagedBranch branch && Values(branch.Condition, Transfer(address)) is { Count: > 0 } values
                && values.Select(v => v.Value != 0).Distinct().ToArray() is [var taken])
                blocks[address][^1] = new ManagedJump(branch.Address, taken ? branch.Taken : branch.Fallthrough);
    }
}
