
namespace Cpp2CS.Extensions.SourceView;

/// <summary>以已证明的原生 Current 字段读取合并单入口路径中的元素快照。</summary>
internal static class SourceEnumeratorSnapshots
{
    internal static ManagedBody Rewrite(ManagedBody body, Func<FieldValue, bool> currentField,
        Func<FieldValue, bool> pureField, Func<FieldValue, LocalValue> temporary)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address, b => b.Statements.ToList());
        var incoming = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (e.Target, Block: b.Address)))
            .GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Select(e => e.Block).ToArray());
        var handlers = body.Regions.Select(r => r.HandlerEntry).ToHashSet();
        bool SameRegion(ulong a, ulong b) => body.Regions.All(r => r.Try.Contains(a) == r.Try.Contains(b) && r.Handler.Contains(a) == r.Handler.Contains(b));
        bool ReadOnly(ManagedValue value) => value switch
        {
            LocalValue { Type: not ByRefRef } or ArgumentValue { Type: not ByRefRef } or ConstantValue => true,
            FieldValue field => (field.Accessor is null || pureField(field))
                && ReadOnly(field.Receiver is AddressValue address ? address.Target : field.Receiver),
            ComparisonValue comparison => ReadOnly(comparison.Left) && ReadOnly(comparison.Right),
            NegatedValue negated => ReadOnly(negated.Operand),
            ConversionValue conversion => ReadOnly(conversion.Operand),
            _ => false,
        };
        FieldValue? Current(ManagedValue value) => ManagedValues.Walk(value).OfType<FieldValue>().FirstOrDefault(field =>
            field.Receiver is AddressValue { Target: LocalValue { Type: DefinitionRef { Definition.IsValueType: true } } }
            && field.Type is not ByRefRef && currentField(field));
        ManagedValue[] Reads(ManagedStatement statement) => statement switch
        {
            ManagedAssignment assignment when ReadOnly(assignment.Value) => [assignment.Value],
            ManagedBranch { Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0 } branch when ReadOnly(branch.Condition) => [branch.Condition],
            ManagedJump jump when jump.Edge.Copies.All(copy => ReadOnly(copy.Value)) => jump.Edge.Copies.Select(copy => copy.Value).ToArray(),
            _ => [],
        };
        foreach (var source in body.Blocks)
            foreach (var original in source.Statements)
            {
                var firstIndex = blocks[source.Address].IndexOf(original);
                if (firstIndex < 0 || Reads(original).Select(Current).FirstOrDefault(f => f is not null)
                    is not { Receiver: AddressValue { Target: LocalValue receiver } } field) continue;
                var uses = new List<(ulong Block, int Index, ManagedStatement Read)>();
                var pending = new Stack<(ulong Address, int Index)>();
                pending.Push((source.Address, firstIndex));
                var visited = new HashSet<ulong>();
                while (pending.TryPop(out var point))
                {
                    var (address, index) = point;
                    if (!visited.Add(address)) continue;
                    for (; index < blocks[address].Count; index++)
                    {
                        var statement = blocks[address][index];
                        if (statement is ManagedAssignment written && written.Target.Variable == receiver.Variable) break;
                        if (Reads(statement).Any(value => Equals(Current(value), field))) uses.Add((address, index, statement));
                        if (statement is ManagedAssignment assignment && assignment.Target.Variable != receiver.Variable
                            && ReadOnly(assignment.Value))
                        {
                            continue;
                        }
                        var edges = statement switch
                        {
                            ManagedJump { Edge.Copies.Count: 0 } jump => new[] { jump.Edge },
                            ManagedBranch { Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0 } branch when ReadOnly(branch.Condition)
                                => [branch.Taken, branch.Fallthrough],
                            _ => [],
                        };
                        foreach (var edge in edges)
                            if (incoming.GetValueOrDefault(edge.Target) is [var predecessor] && predecessor == address
                                && !handlers.Contains(edge.Target) && SameRegion(source.Address, edge.Target)
                                && blocks.TryGetValue(edge.Target, out var target) && target.Count != 0)
                                pending.Push((edge.Target, 0));
                        break;
                    }
                }
                if (uses.Count < 2) continue;
                var snapshot = temporary(field);
                ManagedValue Replace(ManagedValue value) => Equals(value, field) ? snapshot : ManagedValues.Map(value, Replace);
                foreach (var use in uses) blocks[use.Block][use.Index] = ManagedValues.Map(use.Read, Replace);
                blocks[source.Address].Insert(firstIndex, new ManagedAssignment(original.Address, snapshot, field));
            }
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = blocks[b.Address] }).ToArray() };
    }
}
