using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>以已证明的原生 Current 字段读取合并直线路径中的元素快照。</summary>
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
            _ => false,
        };
        FieldValue? Current(ManagedValue value)
        {
            while (value is FieldValue field)
            {
                if (field.Receiver is AddressValue { Target: LocalValue { Type: DefinitionRef { Definition.IsValueType: true } } }
                    && field.Type is not ByRefRef && currentField(field)) return field;
                value = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            }
            return null;
        }
        foreach (var source in body.Blocks)
        foreach (var original in source.Statements.OfType<ManagedAssignment>())
        {
            var firstIndex = blocks[source.Address].IndexOf(original);
            if (firstIndex < 0 || Current(original.Value) is not { Receiver: AddressValue { Target: LocalValue receiver } } field) continue;
            var uses = new List<(ulong Block, int Index, ManagedAssignment Read)>();
            var address = source.Address;
            var index = firstIndex;
            var visited = new HashSet<ulong> { address };
            while (true)
            {
                var statement = blocks[address][index];
                if (statement is ManagedAssignment assignment && assignment.Target.Variable != receiver.Variable
                    && ReadOnly(assignment.Value))
                {
                    if (Equals(Current(assignment.Value), field)) uses.Add((address, index, assignment));
                    index++;
                    if (index < blocks[address].Count) continue;
                }
                else if (statement is ManagedJump { Edge: { Copies.Count: 0 } edge }
                    && incoming.GetValueOrDefault(edge.Target) is [var predecessor] && predecessor == address
                    && !handlers.Contains(edge.Target) && SameRegion(source.Address, edge.Target)
                    && blocks.TryGetValue(edge.Target, out var target) && target.Count != 0 && visited.Add(edge.Target))
                { address = edge.Target; index = 0; continue; }
                break;
            }
            if (uses.Count < 2) continue;
            var snapshot = temporary(field);
            ManagedValue Replace(ManagedValue value) => Equals(value, field) ? snapshot : ManagedValues.Map(value, Replace);
            foreach (var use in uses) blocks[use.Block][use.Index] = use.Read with { Value = Replace(use.Read.Value) };
            blocks[source.Address].Insert(firstIndex, new ManagedAssignment(original.Address, snapshot, field));
        }
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = blocks[b.Address] }).ToArray() };
    }
}
