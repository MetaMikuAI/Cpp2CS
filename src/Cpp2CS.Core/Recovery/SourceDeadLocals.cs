using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>按正常后继和所有外层处理器计算局部存活；只删除无副作用的复制。</summary>
internal static class SourceDeadLocals
{
    internal static ManagedBody Rewrite(ManagedBody body)
    {
        static HashSet<Variable> Reads(IEnumerable<ManagedValue> values) => values.SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        static bool Pure(ManagedValue value) => value is LocalValue or ConstantValue;
        var addressed = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var live = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<Variable>());
        var handlers = body.Blocks.ToDictionary(b => b.Address, b => body.Regions.Where(r => r.Try.Contains(b.Address)).Select(r => r.HandlerEntry).ToArray());
        bool Keep(ManagedCopy copy, HashSet<Variable> after) => after.Contains(copy.Target.Variable) || addressed.Contains(copy.Target.Variable) || !Pure(copy.Value);
        HashSet<Variable> Edge(ManagedEdge edge)
        {
            var after = live[edge.Target]; var before = after.Except(edge.Copies.Select(c => c.Target.Variable)).ToHashSet();
            before.UnionWith(Reads(edge.Copies.Where(c => Keep(c, after)).Select(c => c.Value))); return before;
        }
        HashSet<Variable> Transfer(ManagedBlock block, HashSet<ManagedStatement>? dead = null)
        {
            var state = block.Statements.SelectMany(ManagedValues.Edges).SelectMany(Edge).ToHashSet();
            var exceptional = handlers[block.Address].SelectMany(a => live[a]).ToHashSet();
            foreach (var statement in block.Statements.Reverse())
            {
                state.UnionWith(exceptional);
                if (statement is ManagedAssignment assignment)
                {
                    if (!state.Contains(assignment.Target.Variable) && !addressed.Contains(assignment.Target.Variable) && Pure(assignment.Value)) dead?.Add(statement);
                    else { state.Remove(assignment.Target.Variable); state.UnionWith(Reads([assignment.Value])); }
                }
                else
                {
                    if (statement is ManagedCall { Result: { } result }) state.Remove(result.Variable);
                    if (statement is ManagedAwait { Result: { } awaited }) state.Remove(awaited.Variable);
                    state.UnionWith(Reads(ManagedValues.Of(statement)));
                }
                state.UnionWith(exceptional);
            }
            return state;
        }
        bool changed;
        do
        {
            changed = false;
            foreach (var block in body.Blocks.Reverse())
            {
                var before = Transfer(block);
                if (live[block.Address].SetEquals(before)) continue;
                live[block.Address] = before; changed = true;
            }
        } while (changed);
        var removed = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
        foreach (var block in body.Blocks) Transfer(block, removed);
        return body with { Blocks = body.Blocks.Select(block => block with { Statements = block.Statements.Where(s => !removed.Contains(s))
            .Select(s => ManagedValues.MapEdges(s, edge => edge with { Copies = edge.Copies.Where(c => Keep(c, live[edge.Target])).ToArray() })).ToArray() }).ToArray() };
    }
}
