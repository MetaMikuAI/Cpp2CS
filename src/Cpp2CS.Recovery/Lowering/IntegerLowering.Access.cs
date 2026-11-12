using Cpp2CS.Recovery.Binding;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private void CheckBody(ManagedBody body)
    {
        void Missing(string category) => Fail<object>(LoweringFailureKind.UnsupportedType,
            "访问缺少权限或内联逆证明：" + category, code: "lowering.Access." + category);
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            position = statement.Address;
            if (statement is ManagedCall call && !ManagedAccess.Method(types, method.Method.Owner,
                call.Invocation.Method, call.Invocation.Receiver?.Type)) { Missing("Method"); return; }
            foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk))
            {
                bool referenceBits = value switch
                {
                    ConversionValue conversion => ReferenceType(conversion.Operand.Type),
                    BinaryValue binary => ReferenceType(binary.Left.Type) || ReferenceType(binary.Right.Type),
                    UnaryValue unary => ReferenceType(unary.Operand.Type),
                    _ => false,
                };
                if (referenceBits)
                {
                    Fail<object>(LoweringFailureKind.UnsupportedType, "引用位型用于数值，缺少路径上的零值证明", code: "lowering.ReferenceBits");
                    return;
                }
                if (!ManagedAccess.Type(types, method.Method.Owner, value.Type)) { Missing("Type"); return; }
                if (value is FieldValue field && !ManagedAccess.Field(types, method, field.Field, field.Receiver.Type))
                { Missing("Field");
                    if (types.Kind(field.Field.DeclaringType) == TypeKind.Struct) failure = failure! with { StructType = field.Field.DeclaringType };
                    else if (types.Kind(field.Type) == TypeKind.Struct) failure = failure! with { StructType = field.Type };
                    return; }
                if (value is StaticFieldValue shared && !ManagedAccess.Field(types, method, shared.Field, null))
                { Missing("Field");
                    if (types.Kind(shared.Type) == TypeKind.Struct) failure = failure! with { StructType = shared.Type };
                    return; }
                if (value is NewObjectValue created && !ManagedAccess.Method(types, method.Method.Owner, created.Constructor, null))
                { Missing("Method"); return; }
            }
        }
    }

    private sealed class ReadDefinition(MemoryRead read)
    {
        public MemoryRead Read { get; } = read;
        public LocalValue? Local { get; set; }
        public ManagedValue? Value { get; set; }
        public ManagedValue? Constant { get; set; }
    }
    private readonly Dictionary<Term, ReadDefinition> readValues = [];
    private readonly Dictionary<ReadIdentity, ReadDefinition> readDefinitions = [];
    private readonly Dictionary<ulong, List<(int Before, ReadIdentity Read, ulong Address)>> readInsertions = [];
    private static bool ReferenceType(TypeRef type) => ManagedTypes.IsReferenceType(type) || type is ByRefRef;
    private TypeRef? StaticType(Term term)
    {
        if (arguments.TryGetValue(term, out var argument)) return argument.Type;
        if (locations is null) return null;
        var result = context.Get(locations.Types, term);
        return result.IsSuccess ? result.Value?.Type : null;
    }
    private ManagedValue Coerce(ManagedValue value, TypeRef type)
    {
        if (value is ConstantValue { Bits: 0 } && ManagedTypes.IsReferenceType(type))
            return new ConstantValue(0, type, types.PointerSize * 8);
        if (Equals(value.Type, type) || ManagedTypes.IsReferenceType(value.Type) && types.IsAssignable(value.Type, type)) return value;
        Fail<object>(LoweringFailureKind.UnsupportedType, "值的托管类型与使用位置不兼容");
        return value;
    }
    private void RegisterRead(MemoryRead read)
    {
        if (readDefinitions.ContainsKey(read.Identity)) return;
        // 只登记可用身份；未使用读取的失败不阻断下降，实际使用处负责传播失败。
        var address = context.Get(state.Resolve, read.Address);
        if (!address.IsSuccess) return;
        var location = context.Get(state.Locations, new(address.Value, read.Width));
        if (!location.IsSuccess) return;
        if (location.Value.Region == Region.Frame) return;
        var resolved = context.Get(state.Read, read.Identity);
        if (!resolved.IsSuccess) return;
        if (resolved.Value.Identity is not MemoryAtom { Location.Region: not Region.Frame }) return;
        if (!readValues.TryGetValue(resolved.Value, out var definition))
            readValues.Add(resolved.Value, definition = new(read));
        readDefinitions.Add(read.Identity, definition);
    }
    private ManagedValue? ReadValue(ReadDefinition definition)
    {
        if (definition.Local is not null) return definition.Local;
        if (definition.Constant is not null) return definition.Constant;
        var read = definition.Read;
        // 字符串字面量的槽位在元数据初始化之后就是那个驻留的字符串对象，与 ldstr 相同；它是常量，不需要落进局部。
        if (valueNames is not null && context.Get(valueNames, read.Result) is { IsSuccess: true } named
            && named.Value.Name is EntityName { Entity: StringEntity literal })
            return definition.Constant = new StringValue(literal.Value, types.String, types.PointerSize * 8);
        var usePosition = position; position = read.Trace?.NativeAddress ?? position;
        var value = Access(read.Address, read.Width);
        if (value is null) return null;
        if (types.Kind(value.Type) == TypeKind.Struct)
            return StructScalarFailure(value.Type);
        position = usePosition;
        definition.Value = value;
        definition.Local = new(new(nextLocal++), value.Type, value.Width);
        return definition.Local;
    }
    private ManagedBlock InsertReads(ManagedBlock block)
    {
        if (!readInsertions.TryGetValue(block.Address, out var reads)) return block;
        var statements = new List<ManagedStatement>(); int cursor = 0;
        for (int i = 0; i <= block.Statements.Count; i++)
        {
            while (cursor < reads.Count && reads[cursor].Before == i)
            {
                var read = reads[cursor++];
                if (readDefinitions.TryGetValue(read.Read, out var definition) && definition.Local is { } local)
                    statements.Add(new ManagedAssignment(read.Address, local, definition.Value!));
                if (structReads.TryGetValue(read.Read, out var aggregates))
                    foreach (var aggregate in aggregates)
                        statements.Add(new ManagedAssignment(read.Address, aggregate.Local!, aggregate.Value!));
            }
            if (i < block.Statements.Count) statements.Add(block.Statements[i]);
        }
        return block with { Statements = statements };
    }
    private ManagedStatement? LowerStore(MemoryWrite write, Point point)
    {
        if (structReturnStores is not null)
        {
            var output = context.Get(structReturnStores, write.Identity);
            if (!output.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "结构体结果区写入查询失败", output.Why, "lowering.Struct.ResultStore");
            if (output.Value) return null;
        }
        var resolved = context.Get(state.Resolve, write.Address);
        if (!resolved.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "写入地址查询失败", resolved.Why);
        var location = context.Get(state.Locations, new(resolved.Value, write.Width));
        if (!location.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.State, "写入位置查询失败", location.Why);
        if (location.Value.Region == Region.Frame) return null;
        TypeRef? copiedType = null;
        if (locations is not null && context.Get(locations, new(write.Address, write.Width)) is { IsSuccess: true } located)
            foreach (var view in located.Value.Views.Where(v => v.Offset == 0 && types.Kind(v.Type) == TypeKind.Struct
                && types.StorageBits(v.Type) == write.Width).OrderBy(v => v.Path.Length))
            {
                var copy = context.Get(structs, new(view.Type, new TermSource(write.Value), point));
                if (copy.IsSuccess)
                { copiedType = view.Type; break; }
            }
        var target = Access(write.Address, write.Width, true, copiedType);
        if (target is null) return null;
        if (target is ArrayLengthValue) return Fail<ManagedStatement>(LoweringFailureKind.NonFrameWrite, "数组长度不可写");
        var value = types.Kind(target.Type) == TypeKind.Struct
            ? StructValue(new TermSource(write.Value), target.Type, point)
            : Value(write.Value, IsFloat(target.Type));
        if (value is null) return null;
        value = types.Kind(target.Type) == TypeKind.Struct ? value : ReferenceType(target.Type) ? Coerce(value, target.Type) : IsFloat(target.Type) ? FloatBits(value, write.Width)
            : new ConversionValue(ManagedTypes.IsSigned(target.Type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                value, target.Type, write.Width);
        return new ManagedStore(position, target, value);
    }
    private ManagedValue? Access(Term address, int width, bool write = false, TypeRef? expectedType = null)
    {
        var kind = write ? LoweringFailureKind.NonFrameWrite : LoweringFailureKind.NonFrameRead;
        if (locations is null) return Fail<ManagedValue>(kind, "未装配托管位置查询");
        var result = context.Get(locations, new(address, width));
        if (!result.IsSuccess) return Fail<ManagedValue>(kind, "定位查询失败", result.Why, result.Why?.Code);
        var location = result.Value;
        if (location.Kind is ManagedLocationKind.NotManaged or ManagedLocationKind.Unknown)
            return Fail<ManagedValue>(kind, "使用未定位的内存：" + location.Kind,
                location.Why, location.Why?.Code ?? "lowering.Location." + location.Kind);
        var exact = location.Views.Where(v => (expectedType is null || v.Type.Equals(expectedType)) && v.Offset == 0 && (v.Kind == ManagedLocationKind.ArrayLength
            || types.Size(v.Type) * 8 == width)).ToArray();
        var views = exact.Where(v => v.Kind == ManagedLocationKind.ArrayLength || IntegerType(v.Type) || IsFloat(v.Type) || ReferenceType(v.Type)).ToArray();
        if (views.Length == 0)
        {
            views = exact.Where(v => types.Kind(v.Type) == TypeKind.Struct).OrderBy(v => v.Path.Length).ToArray();
            if (views.Length > 1 && views.Skip(1).All(v => v.Path.Take(views[0].Path.Length).SequenceEqual(views[0].Path)))
                views = [views[0]];
        }
        if (views.Length != 1) return Fail<ManagedValue>(kind,
            views.Length == 0 ? "访问只覆盖位置的一部分" : "访问有多个完整托管视图", code: views.Length == 0 ? "lowering.Location.Partial" : "lowering.Location.Ambiguous");
        var view = views[0];
        if (write && view.Kind == ManagedLocationKind.ArrayLength)
            return Fail<ManagedValue>(kind, "数组长度不可写", code: "lowering.Location.Readonly");
        // 只读字段只能在所属类型的构造函数里写：实例字段是实例构造函数，静态字段是静态构造函数。
        if (write && view.Path.Any(f => (f.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(method.Method.Name == ((f.Field.Attributes & System.Reflection.FieldAttributes.Static) != 0 ? ".cctor" : ".ctor")
                && method.Method.Owner == f.Field.Owner)))
            return Fail<ManagedValue>(kind, "只读字段的写入缺少构造函数上下文", code: "lowering.Location.Readonly");
        return AccessView(view, write);
    }
    private ManagedValue? AccessView(LocationView view, bool write = false)
    {
        if (view.Kind == ManagedLocationKind.StaticField)
        {
            // 根是类的静态字段块，不是托管值；路径的第一项就是静态字段本身。
            var head = view.Path[0];
            var headType = head.Field.Type.Substitute((head.DeclaringType as DefinitionRef)?.Arguments ?? [], []);
            ManagedValue storage = new StaticFieldValue(head, headType, types.ValueWidth(headType));
            foreach (var field in view.Path.Skip(1))
            {
                if (write && types.Kind(storage.Type) == TypeKind.Struct) storage = new AddressValue(storage, types.PointerSize * 8);
                var type = field.Field.Type.Substitute((field.DeclaringType as DefinitionRef)?.Arguments ?? [], []);
                storage = new FieldValue(storage, field, type, types.ValueWidth(type));
            }
            if (!IntegerType(storage.Type) && !IsFloat(storage.Type) && !ReferenceType(storage.Type) && types.Kind(storage.Type) != TypeKind.Struct)
                return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "访问的值类型尚未下降");
            return storage;
        }
        var root = Value(view.Root);
        if (root is null) return null;
        if (view.Kind == ManagedLocationKind.Indirect) return new IndirectValue(root, view.Type, types.ValueWidth(view.Type));
        if (root.Type is ByRefRef { Element: not DefinitionRef { Definition.IsValueType: true } })
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "字段接收者的托管地址必须指向值类型");
        if (view.Kind == ManagedLocationKind.ArrayLength) return Mask(new ArrayLengthValue(root, types.UInt32, 32), view.Width);
        ManagedValue value = root;
        if (view.Kind == ManagedLocationKind.ArrayElement)
        {
            var index = Value(view.Index!);
            if (index is null) return null;
            var element = view.ElementType ?? view.Type;
            value = new ArrayElementValue(root, index, element, types.ValueWidth(element));
        }
        foreach (var field in view.Path)
        {
            if (write && types.Kind(value.Type) == TypeKind.Struct) value = new AddressValue(value, types.PointerSize * 8);
            var type = field.Field.Type.Substitute((field.DeclaringType as DefinitionRef)?.Arguments ?? [], []);
            value = new FieldValue(value, field, type, types.ValueWidth(type));
        }
        if (!IntegerType(value.Type) && !IsFloat(value.Type) && !ReferenceType(value.Type) && types.Kind(value.Type) != TypeKind.Struct)
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "访问的值类型尚未下降");
        return value;
    }
}
