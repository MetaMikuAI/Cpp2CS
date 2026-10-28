using Cpp2CS.Calls;
using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

public sealed partial class SourceLibraryCalls
{
    private readonly Dictionary<TypeDef, FieldAccessor?> collectionCounts = [];

    // List/Queue 的长度不依赖元素类型。全部已登记实例的原生代码须相同，
    // 且实际恢复体严格为单字段读取；不按字段名猜测，也不改写字段写入或地址。
    private FieldAccessor? CollectionCount(FieldValue field, TypeDef caller)
    {
        if (field.Receiver is not (LocalValue or ArgumentValue)
            || field.Field.DeclaringType is not DefinitionRef { Arguments.Count: 1 } owner
            || owner.Definition != types.CorlibDefinition("System.Collections.Generic.List")
                && owner.Definition != types.CorlibDefinition("System.Collections.Generic.Queue")) return null;
        if (!collectionCounts.TryGetValue(owner.Definition, out var shape))
        {
            shape = null;
            var getter = owner.Definition.Properties.SingleOrDefault(p => p.Name == "Count")?.Getter;
            var instances = facts.Code.Functions.SelectMany(fn => facts.EntriesAt(fn.Start)
                .Where(e => e is { Kind: EntryKind.GenericMethod, Method: { } m } && m.Method == getter)
                .Select(e => (Method: e.Method!, Function: fn))).ToArray();
            if (getter is { IsStatic: false, Parameters.Count: 0 } && instances.Length > 0)
            {
                var first = instances[0];
                var bytes = facts.Model.Image.ReadUpTo(first.Function.Start, checked((int)first.Function.Size)).ToArray();
                if (instances.All(p => p.Function.Size == first.Function.Size
                    && facts.Model.Image.ReadUpTo(p.Function.Start, bytes.Length).SequenceEqual(bytes))
                    && summaries.Find(new(first.Method, first.Function.Start, RecoveryMode.Instance))?.Body is { } body)
                    shape = FieldAccessor.Recognize(body, false, types);
            }
            collectionCounts[owner.Definition] = shape;
        }
        if (shape is null || shape.Field.Field != field.Field.Field || !shape.ValueType.Equals(field.Type)
            || shape.Width != field.Width) return null;
        var method = new MethodRef(shape.Method.Method, owner.Arguments, []);
        return ManagedAccess.Method(types, caller, method, field.Receiver.Type)
            ? shape with { Method = method, Field = field.Field } : null;
    }
}
