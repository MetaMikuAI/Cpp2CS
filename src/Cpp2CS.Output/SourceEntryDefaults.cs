using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>InitLocals 已承担入口局部清零；源码视图不再让重复清零阻断状态分派识别。</summary>
internal static class SourceEntryDefaults
{
    public static HashSet<ManagedStatement> Find(ManagedBody body)
    {
        var result = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var incoming = body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges)
            .GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Count());
        var handlers = body.Regions.Select(r => r.HandlerEntry).ToHashSet();
        var first = body.Blocks[0].Address;
        var current = first;
        var visited = new HashSet<ulong>();
        while (visited.Add(current) && incoming.GetValueOrDefault(current) == (current == first ? 0 : 1)
            && !handlers.Contains(current))
        {
            ulong? next = null;
            foreach (var statement in blocks[current].Statements)
            {
                if (statement is ManagedAssignment { Target: var local, Value: ConstantValue { Bits: 0 } zero }
                        && local.Type.Equals(zero.Type)
                    || statement is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue target } } location,
                        Value: ComposedValue { Leaves.Count: 0 } empty }
                        && target.Type.Equals(location.Type) && target.Type.Equals(empty.Type))
                    result.Add(statement);
                else if (statement is ManagedJump { Edge.Copies.Count: 0 } jump) next = jump.Edge.Target;
                else return result;
            }
            if (next is null) break;
            current = next.Value;
        }
        return result;
    }
}
