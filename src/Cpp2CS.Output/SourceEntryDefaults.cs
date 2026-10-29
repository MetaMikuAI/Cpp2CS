using Cpp2CS.Recovery;
using Cpp2CS.Ir;

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
        var assigned = new HashSet<Variable>();
        while (visited.Add(current) && incoming.GetValueOrDefault(current) == (current == first ? 0 : 1)
            && !handlers.Contains(current))
        {
            ulong? next = null;
            foreach (var statement in blocks[current].Statements)
            {
                if (statement is ManagedAssignment { Target: var local, Value: ConstantValue { Bits: 0 } zero }
                        && local.Type.Equals(zero.Type) && !assigned.Contains(local.Variable)
                    || statement is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue target } } location,
                        Value: ComposedValue { Leaves.Count: 0 } empty }
                        && target.Type.Equals(location.Type) && target.Type.Equals(empty.Type) && !assigned.Contains(target.Variable))
                    result.Add(statement);
                // 捕获字段和状态读取不观察其他局部值；已经赋值的目标不能再按默认值消除重置。
                else if (statement is ManagedAssignment { Target: var captured, Value: FieldValue
                    { Receiver: ArgumentValue { Index: -1 }, Accessor: null } }) assigned.Add(captured.Variable);
                else if (statement is ManagedJump { Edge.Copies.Count: 0 } jump) next = jump.Edge.Target;
                else return result;
            }
            if (next is null) break;
            current = next.Value;
        }
        return result;
    }
}
