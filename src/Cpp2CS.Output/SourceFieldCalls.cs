using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

public sealed partial class SourceLibraryCalls
{
    private sealed record FieldCall(MethodRef Method, FieldRef Field, bool Write);
    private readonly Dictionary<DefinitionRef, FieldCall[]> fieldCalls = [];
    private readonly Dictionary<DefinitionRef, SourceValueConstructor[]> valueConstructors = [];
    private Dictionary<MethodRef, ulong>? fieldCallEntries;
    private ILookup<TypeRef, MethodDef>? staticFieldReaders;

    // 只用实际原生方法的单字段读写形态认回可访问入口，不按属性名猜字段。
    private FieldCall[] FieldCalls(DefinitionRef type)
    {
        if (fieldCalls.TryGetValue(type, out var cached)) return cached;
        var found = new List<FieldCall>();
        var constructors = new List<SourceValueConstructor>();
        staticFieldReaders ??= facts.Model.Methods.Where(m => m.IsStatic && m.Parameters.Count == 1 && m.Address != 0
            && m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0 && !ManagedTypes.IsVoid(m.ReturnType))
            .ToLookup(m => m.Parameters[0].Type);
        var candidates = type.Definition.Methods.Concat(type.Arguments.Count == 0 ? staticFieldReaders[type] : []).Distinct();
        foreach (var method in candidates.Where(m => m.GenericParameters.Count == 0
            && m.Name != ".cctor" && (m.Name != ".ctor" || type.Definition.IsValueType)
            && (m.Parameters.Count <= 1 || m.Name == ".ctor" && m.Parameters.Count <= 8)
            && (!m.IsVirtual || (m.Attributes & System.Reflection.MethodAttributes.Final) != 0)
            && (m.Attributes & System.Reflection.MethodAttributes.MemberAccessMask) is System.Reflection.MethodAttributes.Public
                or System.Reflection.MethodAttributes.Family or System.Reflection.MethodAttributes.FamORAssem))
        {
            var reference = new MethodRef(method, method.Owner == type.Definition ? type.Arguments : [], []);
            var entry = method.Address;
            if (type.Arguments.Count != 0)
            {
                fieldCallEntries ??= facts.Code.Functions.SelectMany(fn => facts.EntriesAt(fn.Start)
                    .Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null).Select(e => (Method: e.Method!, Entry: fn.Start)))
                    .GroupBy(p => p.Method).ToDictionary(g => g.Key, g => g.First().Entry);
                var shared = new MethodRef(method, type.Arguments.Select(a => ManagedTypes.IsReferenceType(a) ? (TypeRef)types.Object : a).ToArray(), []);
                if (!fieldCallEntries.TryGetValue(reference, out entry) && !fieldCallEntries.TryGetValue(shared, out entry))
                {
                    // Nullable 的单字段入口可能只保留了另一个同布局实例；仍须恢复并证明单字段读写。
                    if (type.Definition is not { Assembly: "mscorlib.dll", FullName: "System.Nullable" }
                        || facts.Layouts.Of(type) is not { } expected) continue;
                    entry = fieldCallEntries.FirstOrDefault(p => p.Key.Method == method
                        && p.Key.DeclaringType is DefinitionRef instance && facts.Layouts.Of(instance) is { } layout
                        && layout.Fields.Count == expected.Fields.Count && layout.Fields.Zip(expected.Fields).All(pair =>
                            pair.First.Field == pair.Second.Field && pair.First.Offset == pair.Second.Offset
                            && types.Size(pair.First.Type) == types.Size(pair.Second.Type)
                            && types.Kind(pair.First.Type) == types.Kind(pair.Second.Type))).Value;
                }
            }
            if (entry == 0 || facts.Code.At(entry) is not { Region: CodeRegion.Managed, Size: <= 128 }) continue;
            var recovered = type.Arguments.Count == 0 ? recovery.Recover(reference, entry) : recovery.RecoverInstance(reference, entry);
            if (recovered.Body is not { Regions.Count: 0 } original) continue;
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
            if (body.Blocks is [{ Statements: var sequence }] && sequence.LastOrDefault() is ManagedReturn { Value: null }
                && values.Values.SelectMany(ManagedValues.Walk).All(v => v is ArgumentValue or ConstantValue)
                && SourceValueConstructor.Create(reference, stores) is { } constructor) constructors.Add(constructor);
            if (types.Kind(method.ReturnType.Substitute(type.Arguments, [])) == TypeKind.Bool
                && returned is ConversionValue { Kind: ConvKind.Truncate, Operand: ConversionValue { Kind: ConvKind.ZeroExtend, Operand: var boolean } } narrowed
                && narrowed.Width == boolean.Width && types.Kind(boolean.Type) == TypeKind.Bool) returned = boolean;
            FieldRef? Storage(ManagedValue value) => value switch
            {
                IndirectValue { Address: AddressValue address } when address.Target.Type.Equals(value.Type) => Storage(address.Target),
                FieldValue { Receiver: ArgumentValue { Index: -1 }, Field: var field } when !method.IsStatic => field,
                FieldValue { Receiver: ArgumentValue { Index: 0 }, Field: var field } when method.IsStatic
                    && method.Parameters.Count == 1 && method.Parameters[0].Type.Equals(type) && field.DeclaringType.Equals(type) => field,
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
            if ((method.Parameters.Count == 0 || method.IsStatic && method.Parameters.Count == 1)
                && stores.Count == 0 && returned is not null && Storage(returned) is { } read
                && returned.Type.Equals(method.ReturnType.Substitute(type.Arguments, [])) && OnlyStorage(read)
                && (method.Parameters.Count == 0 || values.Values.SelectMany(ManagedValues.Walk)
                    .All(v => v is ArgumentValue or ConstantValue or FieldValue or ConversionValue))) found.Add(new(reference, read, false));
            if (method.Parameters.Count == 1 && ManagedTypes.IsVoid(method.ReturnType) && stores is [var write]
                && (method.Name != ".ctor" || type.Definition.Fields.Count(f => !f.IsStatic) == 1)
                && Storage(write.Target) is { } field && write.Value is ArgumentValue { Index: 0 } argument
                && argument.Type.Equals(write.Target.Type) && OnlyStorage(field)) found.Add(new(reference, field, true));
        }
        valueConstructors[type] = constructors.ToArray();
        return fieldCalls[type] = found.ToArray();
    }

    private ManagedBody RewriteFieldCalls(ManagedBody body)
    {
        FieldCall? Find(ManagedValue value, bool write)
        {
            if (FieldAccessor.FieldOf(value) is not { } field || field.Field.Owner == body.Method.Method.Owner
                && ManagedAccess.Field(types, body.Method.Method.Owner, field, FieldAccessor.ReceiverType(value))) return null;
            if (field.DeclaringType is not DefinitionRef declaring) return null;
            var owners = new List<DefinitionRef> { declaring };
            var receiver = FieldAccessor.ReceiverType(value);
            if (receiver is ByRefRef reference) receiver = reference.Element;
            if (receiver is GenericParameterRef parameter) receiver = parameter.ReferenceBase;
            var chain = new List<DefinitionRef>();
            for (var current = receiver as DefinitionRef; current is not null && !chain.Contains(current);
                current = current.Definition.BaseType?.Substitute(current.Arguments, []) as DefinitionRef) chain.Add(current);
            // 派生类可以公开读取继承字段；只沿实际接收者的基类链寻找，静态字段不改变初始化类型。
            if (!field.Field.IsStatic && chain.Contains(declaring)
                && !ManagedAccess.Field(types, body.Method.Method.Owner, field, FieldAccessor.ReceiverType(value)))
                owners.AddRange(chain.TakeWhile(t => !t.Equals(declaring)));
            return owners.SelectMany(FieldCalls).FirstOrDefault(c => c.Write == write && c.Field.Equals(field)
                && c.Method.Method != body.Method.Method
                && ManagedAccess.Method(types, body.Method.Method.Owner, c.Method, FieldAccessor.ReceiverType(value)));
        }
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var output = new List<ManagedStatement>();
            foreach (var statement in block.Statements)
            {
                if (ManagedValues.Edges(statement).Any(e => e.Copies.Count != 0)) { output.Add(statement); continue; }
                NewObjectValue? Construct(ComposedValue composed)
                {
                    if (composed.Type is not DefinitionRef valueType) return null;
                    _ = FieldCalls(valueType);
                    foreach (var constructor in valueConstructors[valueType])
                    {
                        if (!ManagedAccess.Method(types, body.Method.Method.Owner, constructor.Method, null)
                            || constructor.Build(composed) is not { } created) continue;
                        Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{statement.Address:x}\t{body.Method}\t{constructor.Method}");
                        return created;
                    }
                    return null;
                }
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
                    if (value is ComposedValue composed)
                    {
                        if (Construct(composed) is { } created) return created;
                        var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
                        foreach (var (path, original) in composed.Leaves)
                        {
                            var leaf = original;
                            var length = path.Count;
                            // 单字段构造也可位于元组等聚合值的叶子；保持各叶子的求值顺序。
                            while (length > 0 && path[length - 1].DeclaringType is DefinitionRef declaring
                                && FieldCalls(declaring).FirstOrDefault(c => c.Method.Method.Name == ".ctor"
                                    && c.Field.Equals(path[length - 1])
                                    && ManagedAccess.Method(types, body.Method.Method.Owner, c.Method, null)) is { } constructor)
                            {
                                if (length == 1 && composed.Leaves.Count != 1) break;
                                leaf = new NewObjectValue(constructor.Method, [leaf]) { Transparent = true };
                                Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{statement.Address:x}\t{body.Method}\t{constructor.Method}");
                                length--;
                            }
                            if (length == 0) return leaf;
                            leaves.Add((path.Take(length).ToArray(), leaf));
                        }
                        var combined = composed with { Leaves = leaves };
                        return (ManagedValue?)Construct(combined) ?? combined;
                    }
                    var target = value is StaticFieldValue array ? EmptyArrayGetter(array) : null;
                    target ??= Find(value, false)?.Method;
                    if (target is null) return value;
                    var result = new LocalValue(new Variable(Storage.Temp(next--), 1), value.Type, value.Width);
                    output.Add(new ManagedCall(statement.Address, new ManagedInvocation(target,
                        value is FieldValue member && !target.Method.IsStatic ? member.Receiver : null,
                        value is FieldValue argument && target.Method.IsStatic ? [argument.Receiver] : [], false), result, false));
                    Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{statement.Address:x}\t{body.Method}\t{target}");
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
