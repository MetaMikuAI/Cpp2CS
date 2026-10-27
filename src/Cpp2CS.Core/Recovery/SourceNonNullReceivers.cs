using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>沿正常边传播非空或空值事实；重新赋值和取址不沿用旧事实。</summary>
internal static class SourceNonNullReceivers
{
    internal static Dictionary<ManagedStatement, HashSet<ManagedValue>> Read(ManagedBody body, Func<MethodRef, bool>? getter)
        => Read(body, getter, false);

    internal static Dictionary<ManagedStatement, HashSet<ManagedValue>> ReadNull(ManagedBody body) => Read(body, null, true);

    private static Dictionary<ManagedStatement, HashSet<ManagedValue>> Read(ManagedBody body, Func<MethodRef, bool>? getter, bool nullOnly)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var addressed = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).ToHashSet();
        bool Track(ManagedValue value) => value is LocalValue or ArgumentValue && ManagedTypes.IsReferenceType(value.Type) && !addressed.Contains(value);
        void Transfer(HashSet<ManagedValue> known, ManagedStatement statement)
        {
            void Read(ManagedValue value)
            {
                if (!nullOnly && value is FieldValue field && Track(field.Receiver)) known.Add(field.Receiver);
                if (value is ChoiceValue choice) { Read(choice.Condition); return; }
                if (value is BooleanValue boolean) { Read(boolean.Left); return; }
                ManagedValues.Map(value, child => { Read(child); return child; });
            }
            foreach (var value in ManagedValues.Of(statement)) Read(value);
            if (!nullOnly && statement is ManagedCall { Invocation: var invocation } && (invocation.Virtual || getter?.Invoke(invocation.Method) == true)
                && invocation.Receiver is { } receiver && Track(receiver)) known.Add(receiver);
            ManagedValue? target = statement switch
            {
                ManagedAssignment assignment => assignment.Target,
                ManagedCall call => call.Result,
                ManagedAwait awaited => awaited.Result,
                ManagedStore { Target: LocalValue or ArgumentValue } store => store.Target,
                _ => null,
            };
            if (target is null) return;
            var source = statement switch { ManagedAssignment copy => copy.Value, ManagedStore store => store.Value, _ => null };
            var proven = source is not null && (known.Contains(source) || (nullOnly
                ? source is ConstantValue { Bits: 0 } && ManagedTypes.IsReferenceType(source.Type)
                : source is NewObjectValue or NewArrayValue or DelegateValue or StringValue));
            known.Remove(target);
            if (proven && Track(target)) known.Add(target);
        }
        HashSet<ManagedValue> Edge(HashSet<ManagedValue> input, ManagedEdge edge)
        {
            var output = input.ToHashSet();
            foreach (var copy in edge.Copies) output.Remove(copy.Target);
            foreach (var copy in edge.Copies)
                if (Track(copy.Target) && (input.Contains(copy.Value) || nullOnly && copy.Value is ConstantValue { Bits: 0 }
                    && ManagedTypes.IsReferenceType(copy.Value.Type))) output.Add(copy.Target);
            return output;
        }
        var incoming = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (Block: b.Address, Edge: e)))
            .GroupBy(p => p.Edge.Target).ToDictionary(g => g.Key, g => g.ToArray());
        var entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
        var inputs = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ManagedValue>());
        var outputs = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ManagedValue>());
        bool changed;
        do
        {
            changed = false;
            foreach (var block in body.Blocks)
            {
                var state = new HashSet<ManagedValue>();
                if (!entries.Contains(block.Address) && incoming.TryGetValue(block.Address, out var predecessors))
                {
                    state = Edge(outputs[predecessors[0].Block], predecessors[0].Edge);
                    foreach (var predecessor in predecessors.Skip(1)) state.IntersectWith(Edge(outputs[predecessor.Block], predecessor.Edge));
                }
                inputs[block.Address] = state.ToHashSet();
                foreach (var statement in block.Statements) Transfer(state, statement);
                if (outputs[block.Address].SetEquals(state)) continue;
                outputs[block.Address] = state; changed = true;
            }
        } while (changed);
        var result = new Dictionary<ManagedStatement, HashSet<ManagedValue>>(ReferenceEqualityComparer.Instance);
        foreach (var block in body.Blocks)
        {
            var state = inputs[block.Address].ToHashSet();
            foreach (var statement in block.Statements)
            {
                result[statement] = state.ToHashSet();
                Transfer(state, statement);
            }
        }
        return result;
    }
}
