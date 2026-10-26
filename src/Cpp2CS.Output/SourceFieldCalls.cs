using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

public sealed partial class SourceLibraryCalls
{
    private sealed record FieldCall(MethodRef Method, FieldRef Field, bool Write);
    private readonly Dictionary<TypeDef, FieldCall[]> fieldCalls = [];

    // 只用实际原生方法的单字段读写形态认回公开入口，不按属性名猜字段。
    private FieldCall[] FieldCalls(TypeDef type)
    {
        if (fieldCalls.TryGetValue(type, out var cached)) return cached;
        var found = new List<FieldCall>();
        foreach (var method in type.Methods.Where(m => m.Address != 0 && m.GenericParameters.Count == 0 && m.Owner.GenericParameters.Count == 0
            && m.Name is not (".ctor" or ".cctor") && m.Parameters.Count <= 1 && !m.IsVirtual
            && (m.Attributes & System.Reflection.MethodAttributes.MemberAccessMask) == System.Reflection.MethodAttributes.Public
            && facts.Code.At(m.Address) is { Region: CodeRegion.Managed, Size: <= 128 }))
        {
            var reference = new MethodRef(method, [], []);
            if (recovery.Recover(reference, method.Address).Body is not { Regions.Count: 0 } original) continue;
            var body = SourceRewriter.Rewrite(original, types);
            var values = new Dictionary<Variable, ManagedValue>();
            var stores = new List<ManagedStore>();
            ManagedValue? returned = null;
            var valid = true;
            foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
            {
                switch (statement)
                {
                    case ManagedAssignment assignment: values[assignment.Target.Variable] = Expand(assignment.Value, values); break;
                    case ManagedStore store: stores.Add(store with { Target = Expand(store.Target, values), Value = Expand(store.Value, values) }); break;
                    case ManagedReturn result: returned = result.Value is null ? null : Expand(result.Value, values); break;
                    case ManagedJump { Edge.Copies.Count: 0 }: break;
                    default: valid = false; break;
                }
            }
            if (!valid) continue;
            FieldRef? Storage(ManagedValue value) => value switch
            {
                FieldValue { Receiver: ArgumentValue { Index: -1 }, Field: var field } when !method.IsStatic => field,
                StaticFieldValue { Field: var field } when method.IsStatic && field.DeclaringType.Equals(reference.DeclaringType) => field,
                _ => null,
            };
            bool OnlyStorage(FieldRef storage) => values.Values.Select(v => Expand(v, values)).SelectMany(ManagedValues.Walk)
                .Where(v => v is FieldValue or StaticFieldValue).All(v =>
                {
                    while (v is FieldValue component && (component.Receiver is AddressValue a ? a.Target : component.Receiver) is var receiver
                        && types.Kind(receiver.Type) == TypeKind.Struct && receiver is not ArgumentValue { Index: -1 }) v = receiver;
                    return Equals(Storage(v), storage) || method.Parameters.Count == 1 && v is ArgumentValue { Index: 0 };
                });
            if (method.Parameters.Count == 0 && stores.Count == 0 && returned is not null && Storage(returned) is { } read
                && returned.Type.Equals(method.ReturnType) && OnlyStorage(read)) found.Add(new(reference, read, false));
            if (method.Parameters.Count == 1 && ManagedTypes.IsVoid(method.ReturnType) && stores is [var write]
                && Storage(write.Target) is { } field && write.Value is ArgumentValue { Index: 0 } argument
                && argument.Type.Equals(write.Target.Type) && OnlyStorage(field)) found.Add(new(reference, field, true));
        }
        return fieldCalls[type] = found.ToArray();
    }

    private ManagedBody RewriteFieldCalls(ManagedBody body)
    {
        FieldCall? Find(ManagedValue value, bool write)
        {
            if (FieldAccessor.FieldOf(value) is not { } field || ManagedAccess.Field(types, body.Method.Method.Owner, field, FieldAccessor.ReceiverType(value))) return null;
            return FieldCalls(field.Field.Owner).FirstOrDefault(c => c.Write == write && c.Field.Equals(field)
                && ManagedAccess.Method(types, body.Method.Method.Owner, c.Method, FieldAccessor.ReceiverType(value)));
        }
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var output = new List<ManagedStatement>();
            foreach (var statement in block.Statements)
            {
                if (ManagedValues.Edges(statement).Any(e => e.Copies.Count != 0)) { output.Add(statement); continue; }
                ManagedValue Read(ManagedValue value)
                {
                    if (value is AddressValue) return value;
                    if (value is FieldValue field)
                    {
                        var receiver = field.Receiver is AddressValue address
                            ? address with { Target = Read(address.Target) } : Read(field.Receiver);
                        value = field with { Receiver = receiver };
                    }
                    else value = ManagedValues.Map(value, Read);
                    if (Find(value, false) is not { } candidate) return value;
                    var result = new LocalValue(new Variable(Storage.Temp(next--), 1), value.Type, value.Width);
                    output.Add(new ManagedCall(statement.Address, new ManagedInvocation(candidate.Method,
                        value is FieldValue member ? member.Receiver : null, [], false), result, false));
                    Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{statement.Address:x}\t{body.Method}\t{candidate.Method}");
                    return result;
                }
                if (statement is ManagedStore store && Find(store.Target, true) is { } setter)
                {
                    var receiver = store.Target is FieldValue field ? Read(field.Receiver) : null;
                    var value = Read(store.Value);
                    output.Add(new ManagedCall(store.Address, new ManagedInvocation(setter.Method, receiver, [value], false), null, false));
                    Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{statement.Address:x}\t{body.Method}\t{setter.Method}");
                }
                else output.Add(ManagedValues.Map(statement, Read, target => target));
            }
            return block with { Statements = output };
        }).ToArray() };
    }
}
