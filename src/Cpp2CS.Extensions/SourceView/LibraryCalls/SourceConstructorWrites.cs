
namespace Cpp2CS.Extensions.SourceView;

/// <summary>值类型存储的连续完整字段初始化，认回已有纯构造入口。</summary>
internal static class SourceConstructorWrites
{
    internal static ManagedBody Rewrite(ManagedBody body, Func<DefinitionRef, IEnumerable<SourceValueConstructor>> constructors,
        Action<ulong, MethodRef> matched)
    {
        static bool Storage(ManagedValue value) => value switch
        {
            LocalValue or StaticFieldValue { Accessor: null } => true,
            FieldValue { Accessor: null } field => Storage(field.Receiver is AddressValue address ? address.Target : field.Receiver),
            _ => false,
        };
        static (ManagedValue Root, FieldRef Field)? Target(ManagedValue value)
        {
            if (value is not FieldValue field || field.Accessor is { } accessor && (!accessor.Write
                || !accessor.Field.Equals(field.Field) || !accessor.ValueType.Equals(field.Type) || accessor.Width != field.Width)) return null;
            var receiver = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            return Storage(receiver) && receiver.Type.Equals(field.Field.DeclaringType) ? (receiver, field.Field) : null;
        }
        return body with
        {
            Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToList();
            // 嵌套值类型的叶子可能交错写入；完整覆盖时从内到外认回纯构造。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedStore first || Path(first.Target) is not { Root.Type: DefinitionRef type } initial
                    || initial.Fields.Count < 2) continue;
                var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
                for (var end = i; end < statements.Count && end < i + 32; end++)
                {
                    if (statements[end] is not ManagedStore write || Path(write.Target) is not { } target || target.Root != initial.Root
                        || ManagedValues.Walk(write.Value).Any(v => v.Equals(initial.Root))
                        || leaves.Any(p => p.Path.SequenceEqual(target.Fields))) break;
                    leaves.Add((target.Fields, write.Value));
                    if (Build(type, leaves) is not { } created) continue;
                    statements.RemoveRange(i, end - i + 1);
                    statements.Insert(i, initial.Root is LocalValue local ? new ManagedAssignment(first.Address, local, created)
                        : new ManagedStore(first.Address, initial.Root, created));
                    matched(first.Address, created.Constructor);
                    break;
                }
            }
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedStore first || Target(first.Target) is not { } initial
                    || initial.Root.Type is not DefinitionRef { Definition.IsValueType: true } type) continue;
                foreach (var constructor in constructors(type))
                {
                    var writes = statements.Skip(i).Take(constructor.Fields.Count).OfType<ManagedStore>().ToArray();
                    if (writes.Length != constructor.Fields.Count || writes.Any(s => Target(s.Target) is not { } t || t.Root != initial.Root
                        || ManagedValues.Walk(s.Value).Any(v => v.Equals(initial.Root)))) continue;
                    var value = new ComposedValue(type, writes.Select(s => ((IReadOnlyList<FieldRef>)new[] { Target(s.Target)!.Value.Field }, s.Value)).ToArray());
                    if (constructor.Build(value) is not { } created) continue;
                    statements.RemoveRange(i, writes.Length);
                    statements.Insert(i, initial.Root is LocalValue local ? new ManagedAssignment(first.Address, local, created)
                        : new ManagedStore(first.Address, initial.Root, created));
                    matched(first.Address, constructor.Method);
                    break;
                }
            }
            return block with { Statements = statements };
        }).ToArray()
        };

        (ManagedValue Root, IReadOnlyList<FieldRef> Fields)? Path(ManagedValue value)
        {
            var fields = new List<FieldRef>();
            while (value is FieldValue field && field.Field.DeclaringType is DefinitionRef { Definition.IsValueType: true })
            {
                if (field.Accessor is { } accessor && (!accessor.Field.Equals(field.Field)
                    || !accessor.ValueType.Equals(field.Type) || accessor.Width != field.Width)) return null;
                fields.Insert(0, field.Field);
                value = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            }
            return fields.Count > 0 && Storage(value) ? (value, fields) : null;
        }

        NewObjectValue? Build(DefinitionRef type, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves)
        {
            var values = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
            foreach (var group in leaves.GroupBy(p => p.Path[0]))
            {
                var parts = group.ToArray();
                ManagedValue? value = parts is [var whole] && whole.Path.Count == 1 ? whole.Value
                    : parts.All(p => p.Path.Count > 1) && group.Key.Field.Type.Substitute(type.Arguments, []) is DefinitionRef nested
                        ? Build(nested, parts.Select(p => ((IReadOnlyList<FieldRef>)p.Path.Skip(1).ToArray(), p.Value)).ToArray()) : null;
                if (value is null) return null;
                values.Add((new[] { group.Key }, value));
            }
            var composed = new ComposedValue(type, values);
            return constructors(type).Select(c => c.Build(composed)).FirstOrDefault(v => v is not null);
        }
    }
}
