using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>局部结构体的完整字段快照、复制和清零，按值恢复；不跨越其他语句。</summary>
internal static class SourceStructCopies
{
    /// <summary>同一结构体的全部直属字段原样重组，就是该位置的值；只在完整覆盖时折回整体复制。</summary>
    internal static ManagedValue? WholeValue(ComposedValue value)
    {
        if (value.StructType is not DefinitionRef type || value.Leaves.Count == 0) return null;
        var fields = type.Definition.Fields.Where(f => !f.IsStatic).ToHashSet();
        if (fields.Count != value.Leaves.Count) return null;
        ManagedValue? root = null;
        foreach (var (path, leaf) in value.Leaves)
        {
            if (path.Count != 1 || leaf is not FieldValue field || !field.Field.Equals(path[0])
                || !fields.Remove(field.Field.Field)) return null;
            var receiver = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            if (!Stable(receiver) || !receiver.Type.Equals(value.StructType)
                || root is not null && !root.Equals(receiver)) return null;
            root = receiver;
        }
        return root;
    }

    internal static ManagedBody Rewrite(ManagedBody body)
    {
        static LocalValue? Local(ManagedValue value) => value switch
        {
            LocalValue local => local,
            AddressValue { Target: LocalValue local } => local,
            _ => null,
        };
        static ManagedValue? Destination(ManagedValue value) => value is AddressValue { Target: FieldValue { Receiver: LocalValue or ArgumentValue } field }
            ? field : Local(value);
        var uses = body.Blocks.SelectMany(b => b.Statements).SelectMany(s =>
                (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToList();
            // 读取全部直属字段后立即按原字段返回，等价于在原读取位置复制整个结构体。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment { Value: FieldValue { Accessor: null } field }) continue;
                var root = field.Receiver is AddressValue address ? address.Target : field.Receiver;
                if (root.Type is not DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition }
                    || !Stable(root)) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var reads = statements.Skip(i).Take(fields.Count).OfType<ManagedAssignment>().ToArray();
                if (fields.Count == 0 || reads.Length != fields.Count || i + fields.Count >= statements.Count
                    || reads.Any(r => r.Value is not FieldValue { Accessor: null } f || !f.Receiver.Equals(field.Receiver)
                        || !fields.Contains(f.Field.Field) || uses.GetValueOrDefault(r.Target.Variable) != 1)
                    || reads.Select(r => ((FieldValue)r.Value).Field.Field).Distinct().Count() != fields.Count
                    || reads.Select(r => r.Target.Variable).Distinct().Count() != fields.Count
                    || statements[i + fields.Count] is not ManagedReturn { Value: ComposedValue composed } returned
                    || !composed.Type.Equals(root.Type) || composed.Leaves.Count != fields.Count) continue;
                var snapshots = reads.ToDictionary(r => r.Target.Variable, r => ((FieldValue)r.Value).Field);
                if (composed.Leaves.Any(p => p.Path.Count != 1 || p.Value is not LocalValue local
                    || !snapshots.TryGetValue(local.Variable, out var copied) || !copied.Equals(p.Path[0]))
                    || composed.Leaves.Select(p => p.Path[0].Field).Distinct().Count() != fields.Count) continue;
                statements.RemoveRange(i, fields.Count + 1);
                statements.Insert(i, returned with { Value = root });
            }
            // 参数或局部值的完整逐字段写入，折回属性后备字段等存储位置的整体赋值。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedStore { Target: FieldValue { Accessor: null } target,
                        Value: FieldValue { Accessor: null } sourceField } first
                    || Destination(target.Receiver) is not { Type: DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition } } destination) continue;
                var source = sourceField.Receiver is AddressValue address ? address.Target : sourceField.Receiver;
                if (source is not (LocalValue or ArgumentValue) || !source.Type.Equals(destination.Type)) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var writes = statements.Skip(i).Take(fields.Count).OfType<ManagedStore>().ToArray();
                if (fields.Count == 0 || writes.Length != fields.Count || writes.Any(s =>
                    s.Target is not FieldValue { Accessor: null } t || s.Value is not FieldValue { Accessor: null } v
                    || !t.Receiver.Equals(target.Receiver) || !v.Receiver.Equals(sourceField.Receiver) || !t.Field.Equals(v.Field))
                    || !writes.Select(s => ((FieldValue)s.Target).Field.Field).ToHashSet().SetEquals(fields)) continue;
                statements.RemoveRange(i, fields.Count);
                statements.Insert(i, destination is LocalValue local ? new ManagedAssignment(first.Address, local, source)
                    : new ManagedStore(first.Address, destination, source));
            }
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment { Value: FieldValue field } first
                    || Local(field.Receiver) is not { Type: DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition } } source) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var reads = statements.Skip(i).Take(fields.Count).OfType<ManagedAssignment>().ToArray();
                if (fields.Count < 2 || reads.Length != fields.Count || reads.Any(r => r.Value is not FieldValue f || Local(f.Receiver) != source)
                    || !reads.Select(r => ((FieldValue)r.Value).Field.Field).ToHashSet().SetEquals(fields)
                    || reads.Select(r => r.Target.Variable).Distinct().Count() != fields.Count) continue;
                var snapshots = reads.ToDictionary(r => r.Target.Variable, r => (FieldValue)r.Value);
                var destinations = new Dictionary<ManagedValue, HashSet<FieldDef>>();
                var initialized = new HashSet<LocalValue>();
                var consumed = new Dictionary<Cpp2CS.Ir.Variable, int>();
                var end = i + reads.Length;
                while (end < statements.Count)
                {
                    if (statements[end] is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue zero } }, Value: ComposedValue { Leaves.Count: 0 } }
                        && zero.Type.Equals(source.Type) && zero != source && !destinations.ContainsKey(zero)) initialized.Add(zero);
                    else if (statements[end] is ManagedStore { Target: FieldValue target, Value: LocalValue value }
                        && Destination(target.Receiver) is { } destination && destination != source && destination.Type.Equals(source.Type)
                        && snapshots.TryGetValue(value.Variable, out var read) && target.Field.Equals(read.Field))
                    {
                        if (!destinations.TryGetValue(destination, out var copied)) destinations[destination] = copied = [];
                        if (!copied.Add(target.Field.Field)) break;
                        consumed[value.Variable] = consumed.GetValueOrDefault(value.Variable) + 1;
                    }
                    else break;
                    end++;
                }
                // 同一快照可写入多个临时结构体；每个目标都须完整覆盖，字段快照不得流出复制区。
                if (destinations.Count == 0 || initialized.Any(d => !destinations.ContainsKey(d)) || destinations.Values.Any(f => !f.SetEquals(fields))
                    || snapshots.Keys.Any(v => consumed.GetValueOrDefault(v) != uses.GetValueOrDefault(v))) continue;
                statements.RemoveRange(i, end - i);
                statements.InsertRange(i, destinations.Keys.Select(d => d is LocalValue local
                    ? (ManagedStatement)new ManagedAssignment(first.Address, local, source) : new ManagedStore(first.Address, d, source)));
                i += destinations.Count - 1;
            }
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment { Value: FieldValue { Accessor: null } field } first
                    || Local(field.Receiver) is not { Type: DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition } } source) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var reads = statements.Skip(i).Take(fields.Count).OfType<ManagedAssignment>().ToArray();
                if (fields.Count < 2 || reads.Length != fields.Count || reads.Any(r => r.Value is not FieldValue { Accessor: null } f
                    || Local(f.Receiver) != source || !fields.Contains(f.Field.Field) || uses.GetValueOrDefault(r.Target.Variable) != 1)
                    || reads.Select(r => ((FieldValue)r.Value).Field.Field).Distinct().Count() != fields.Count
                    || reads.Select(r => r.Target.Variable).Distinct().Count() != fields.Count) continue;
                var snapshots = reads.ToDictionary(r => r.Target.Variable, r => (FieldValue)r.Value);
                var copied = new HashSet<FieldDef>();
                var cleared = new HashSet<FieldDef>();
                LocalValue? destination = null;
                var end = i + reads.Length;
                ulong clearAddress = 0;
                while (end < statements.Count && statements[end] is ManagedStore { Target: FieldValue { Accessor: null } target } store)
                {
                    var root = Local(target.Receiver);
                    if (root == source && fields.Contains(target.Field.Field) && store.Value is ConstantValue { Bits: 0 })
                    { cleared.Add(target.Field.Field); clearAddress = store.Address; }
                    else if (root is not null && root != source && root.Type.Equals(source.Type)
                        && (destination is null || root == destination) && store.Value is LocalValue value
                        && snapshots.TryGetValue(value.Variable, out var read) && target.Field.Equals(read.Field)
                        && copied.Add(target.Field.Field)) destination = root;
                    else break;
                    end++;
                }
                if (destination is null || !copied.SetEquals(fields) || cleared.Count != 0 && !cleared.SetEquals(fields)) continue;
                statements.RemoveRange(i, end - i);
                statements.Insert(i, new ManagedAssignment(first.Address, destination, source));
                if (cleared.Count != 0)
                {
                    statements.Insert(i + 1, new ManagedStore(clearAddress, new IndirectValue(new AddressValue(source), source.Type), new ComposedValue(source.Type, [])));
                    i++;
                }
            }
            return block with { Statements = statements };
        }).ToArray() };
    }

    private static bool Stable(ManagedValue value) => value switch
    {
        LocalValue or ArgumentValue or ConstantValue => true,
        AddressValue address => Stable(address.Target),
        FieldValue { Accessor: null } field => Stable(field.Receiver),
        ArrayElementValue element => Stable(element.Array) && Stable(element.Index),
        ConversionValue conversion => Stable(conversion.Operand),
        _ => false,
    };
}
