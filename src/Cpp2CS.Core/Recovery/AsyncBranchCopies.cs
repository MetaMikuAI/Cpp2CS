using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>比较只经过纯局部赋值的两条续接路径，边上的 phi 复制按并行赋值处理。</summary>
internal static class AsyncBranchCopies
{
    public static bool Equivalent(ManagedEdge left, ManagedEdge right, IReadOnlyDictionary<ulong, List<ManagedStatement>> blocks,
        Func<ManagedValue, bool> pure)
    {
        (ulong Target, Dictionary<LocalValue, ManagedValue> Values)? Path(ManagedEdge edge)
        {
            var values = new Dictionary<LocalValue, ManagedValue>();
            ManagedValue Value(ManagedValue value) => value is LocalValue local && values.TryGetValue(local, out var copied)
                ? copied : ManagedValues.Map(value, Value);
            void Copies(IReadOnlyList<ManagedCopy> copies)
            {
                var assigned = copies.Select(c => (c.Target, Value: Value(c.Value))).ToArray();
                foreach (var (target, value) in assigned) values[target] = value;
            }
            var seen = new HashSet<ulong>();
            while (seen.Add(edge.Target))
            {
                if (edge.Copies.Any(c => !pure(c.Value))) return null;
                Copies(edge.Copies);
                if (!blocks.TryGetValue(edge.Target, out var statements) || statements.LastOrDefault() is not ManagedJump jump
                    || statements.SkipLast(1).Any(s => s is not ManagedAssignment a || !pure(a.Value))) return (edge.Target, values);
                foreach (var assignment in statements.SkipLast(1).Cast<ManagedAssignment>()) values[assignment.Target] = Value(assignment.Value);
                edge = jump.Edge;
            }
            return null;
        }
        if (Path(left) is not { } first || Path(right) is not { } second || first.Target != second.Target) return false;
        return first.Values.Keys.Concat(second.Values.Keys).Distinct()
            .All(local => first.Values.GetValueOrDefault(local, local).Equals(second.Values.GetValueOrDefault(local, local)));
    }
}
