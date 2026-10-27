using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>局部值类型的连续完整字段初始化，认回已有纯构造入口。</summary>
internal static class SourceConstructorWrites
{
    internal static ManagedBody Rewrite(ManagedBody body, Func<DefinitionRef, IEnumerable<SourceValueConstructor>> constructors,
        Action<ulong, MethodRef> matched)
    {
        static (LocalValue Local, FieldRef Field)? Target(ManagedValue value)
        {
            if (value is not FieldValue field || field.Accessor is { } accessor && (!accessor.Write
                || !accessor.Field.Equals(field.Field) || !accessor.ValueType.Equals(field.Type) || accessor.Width != field.Width)) return null;
            var receiver = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            return receiver is LocalValue local && local.Type.Equals(field.Field.DeclaringType) ? (local, field.Field) : null;
        }
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToList();
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedStore first || Target(first.Target) is not { } initial
                    || initial.Local.Type is not DefinitionRef { Definition.IsValueType: true } type) continue;
                foreach (var constructor in constructors(type))
                {
                    var writes = statements.Skip(i).Take(constructor.Fields.Count).OfType<ManagedStore>().ToArray();
                    if (writes.Length != constructor.Fields.Count || writes.Any(s => Target(s.Target) is not { } t || t.Local != initial.Local
                        || ManagedValues.Walk(s.Value).OfType<LocalValue>().Any(l => l.Variable == initial.Local.Variable))) continue;
                    var value = new ComposedValue(type, writes.Select(s => ((IReadOnlyList<FieldRef>)new[] { Target(s.Target)!.Value.Field }, s.Value)).ToArray());
                    if (constructor.Build(value) is not { } created) continue;
                    statements.RemoveRange(i, writes.Length);
                    statements.Insert(i, new ManagedAssignment(first.Address, initial.Local, created));
                    matched(first.Address, constructor.Method);
                    break;
                }
            }
            return block with { Statements = statements };
        }).ToArray() };
    }
}
