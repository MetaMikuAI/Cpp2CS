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
            if (receiver is not (LocalValue or ArgumentValue) || !receiver.Type.Equals(value.StructType)
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
        var uses = body.Blocks.SelectMany(b => b.Statements).SelectMany(s =>
                (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToList();
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
}
