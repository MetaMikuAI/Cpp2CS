using System.Collections.Immutable;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private readonly List<StructOrigin> structParameters = [];
    private StructValueQuery structs = null!;
    private StructMemoryPartQuery structMemoryParts = null!;
    private readonly Dictionary<(Term Source, LocationView View), LocalValue> structMemoryValues = [];
    private StructReturnStoreQuery? structReturnStores;
    private readonly Dictionary<ReadIdentity, List<ReadDefinition>> structReads = [];
    private readonly Dictionary<(ReadIdentity Read, LocationView Location), LocalValue> structReadValues = [];

    private void PrepareStructs()
    {
        var origins = new List<StructOrigin>(structParameters);
        foreach (var block in function.Blocks)
            for (int i = 0; i < block.Statements.Length; i++)
                if (block.Statements[i] is Call call && callDefinitions.TryGetValue(call.Identity, out var definition)
                    && types.Kind(definition.Method.Concrete(definition.Method.Method.ReturnType)) == TypeKind.Struct
                    && definition.Binding.Result.Source is { } source)
                    origins.Add(new(definition.Method.Concrete(definition.Method.Method.ReturnType), source, new(block.Identity, i + 1), Call: call.Identity));
        structs = new(types, state, locations, origins);
        structMemoryParts = new(state, locations, types);
        if (types.Kind(method.Concrete(method.Method.ReturnType)) == TypeKind.Struct
            && binder.Return(new Return([]), signature, function.Terms, function.Inputs.Select(i => new SlotValue(i.Slot, i.Value)).ToImmutableArray(), function.IncomingArgumentArea)
                .Value?.Source is IndirectSource output)
            structReturnStores = new(state, output.Address, output.Length);
    }
    private ManagedValue? StructOriginValue(StructOrigin origin) => origin.Parameter is { } index
        ? new ArgumentValue(index, origin.Type, 0) : CallResult(callDefinitions[origin.Call!]);

    private ManagedValue? StructPart(Term term, int low, int width)
    {
        var result = context.Get(structs.Parts, new(term, low, width));
        if (!result.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.State, "结构体字段来源查询失败", result.Why);
        if (result.Value is not { } part)
        {
            var memory = context.Get(structMemoryParts, new(term, low, width));
            if (!memory.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.State, "宽读取的字段投影失败", memory.Why, "lowering.Struct.Projection");
            return memory.Value is { } projection ? StructMemoryValue(projection) : null;
        }
        var root = StructOriginValue(part.Origin); if (root is null) return null;
        var projected = ManagedProjections.Project(types, root, part.Projection, field => field);
        if (projected is null) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
            "结构体字段投影与整体布局不符", code: "lowering.Struct.Projection");
        return part.Low == 0 && part.Width == part.Projection.Width ? projected.Value : Slice(projected.Value, part.Low, part.Width);
    }
    private ManagedValue? StructValue(BoundSource source, TypeRef type, Point point)
    {
        if (GenericStruct(type)) return GenericFailure<ManagedValue>("Struct", "含类型参数的值类型尚未下降");
        var value = BuildStructValue(source, type, point);
        if (value is null && failure is { StructType: null } missing) failure = missing with { StructType = type };
        return value;
    }
    private ManagedValue? BuildStructValue(BoundSource source, TypeRef type, Point point)
    {
        var result = context.Get(structs, new(type, source, point));
        if (!result.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
            result.Why!.Message, result.Why, result.Why.Code.StartsWith("lowering.Struct.", StringComparison.Ordinal) ? result.Why.Code : "lowering.Struct.Source");
        var plan = result.Value;
        if (plan.Origin is { } origin) return StructOriginValue(origin);
        if (plan.Location is { } location && plan.Read is { } read)
        {
            var key = (read, location);
            if (structReadValues.TryGetValue(key, out var known)) return known;
            var value = AccessView(location); if (value is null) return null;
            var native = function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Single(r => r.Identity == read);
            var definition = new ReadDefinition(native) { Value = value, Local = new(new(nextLocal++), type, 0) };
            if (!structReads.TryGetValue(read, out var reads)) structReads.Add(read, reads = []);
            reads.Add(definition); structReadValues.Add(key, definition.Local);
            return definition.Local;
        }
        if (source is IndirectSource indirect && BoundTerm(indirect.Address, point) is { } pointer
            && context.Get(state.Resolve, pointer) is { IsSuccess: true } resolved
            && context.Get(state.Locations, new(resolved.Value, 8)) is { IsSuccess: true, Value.Region: Region.Frame })
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "帧上结构体局部缺少整体来源，地址与生存期尚未下降", code: "lowering.Struct.FrameLocal");
        if (failure is not null) return null;
        if (plan.Representation is { } representation)
        {
            if (TokenHandle(type, plan) is { } token) return token;
            if (failure is not null) return null;
            if (!WritableStructPath(representation.Path)) return null;
            var field = types.Kind(representation.Type) == TypeKind.Struct ? StructValue(source, representation.Type, point)
                : StructLeafValue(plan.Leaves[0].Value, representation.Type);
            return field is null ? null : new ComposedValue(type, [(representation.Path, field)]);
        }
        foreach (var leaf in plan.Leaves) if (!WritableStructPath(leaf.Projection.Path)) return null;
        var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        foreach (var leaf in plan.Leaves)
        {
            var value = StructLeafValue(leaf.Value, leaf.Projection.Type); if (value is null) return null;
            leaves.Add((leaf.Projection.Path, value));
        }
        return new ComposedValue(type, leaves);
    }
    private ManagedValue? StructScalarFailure(TypeRef type)
    {
        Fail<object>(LoweringFailureKind.UnsupportedType, "结构体位片跨越多个字段，不能当作标量使用", code: "lowering.Struct.Scalar");
        if (failure is { StructType: null } missing) failure = missing with { StructType = type };
        return null;
    }
    private ManagedValue? StructMemoryValue(StructMemoryPart projection)
    {
        var key = (projection.Source, projection.View);
        if (structMemoryValues.TryGetValue(key, out var known)) return known;
        var value = AccessView(projection.View); if (value is null) return null;
        var local = new LocalValue(new(nextLocal++), value.Type, value.Width);
        structMemoryValues.Add(key, local);
        foreach (var read in projection.Reads)
        {
            var native = function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Single(r => r.Identity == read);
            if (!structReads.TryGetValue(read, out var definitions)) structReads.Add(read, definitions = []);
            definitions.Add(new(native) { Value = value, Local = local });
        }
        return local;
    }
    private bool WritableStructPath(IReadOnlyList<FieldRef> path)
    {
        foreach (var field in path)
        {
            if (!ManagedAccess.Field(types, method, field, field.DeclaringType))
            { Fail<object>(LoweringFailureKind.UnsupportedType, "结构体组成需要不可访问的字段：" + field, code: "lowering.Struct.Inaccessible"); return false; }
            if ((field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
                && !(method.Method.Name == ".ctor" && method.Method.Owner == field.Field.Owner))
            { Fail<object>(LoweringFailureKind.UnsupportedType, "结构体组成需要在构造函数外写只读字段：" + field, code: "lowering.Struct.Readonly"); return false; }
        }
        return true;
    }
    private ManagedValue? StructLeafValue(Term term, TypeRef type)
    {
        var value = Value(term, IsFloat(type));
        if (value is null)
        {
            if (failure is { } cause) failure = cause with { Reason = new("lowering.Struct.Leaf", "结构体叶子的值没有托管写法：" + type, cause.Reason) };
            return null;
        }
        if (ReferenceType(type)) return Coerce(value, type);
        if (IsFloat(type)) return FloatBits(value, types.StorageBits(type));
        if (IntegerType(type) || ManagedTypes.IsNativePointer(type))
            return new ConversionValue(ManagedTypes.IsSigned(type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                IntegerBits(value), type, types.StorageBits(type));
        return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "结构体叶子没有标量托管写法：" + type, code: "lowering.Struct.LeafType");
    }
    private ManagedValue? TokenHandle(TypeRef type, StructPlan plan)
    {
        if (!type.Equals(types.RuntimeTypeHandle) && !type.Equals(types.RuntimeFieldHandle) && !type.Equals(types.RuntimeMethodHandle)) return null;
        // Mono 核心库 mcs/class/corlib/System/Runtime{Type,Field,Method}Handle.cs：唯一实例字段为 IntPtr。
        // libil2cpp vm/Type.cpp::GetTypeFromHandle、icalls/mscorlib/System.Reflection/RuntimeMethodInfo.cpp::GetMethodFromHandleInternalType_native
        // 与 icalls/mscorlib/System.Reflection/FieldInfo.cpp::internal_from_handle_type，分别消费类型、方法、字段的运行时指针。
        if (plan.Leaves.Length != 1 || plan.Leaves[0].Projection.Width != types.PointerSize * 8
            || !ManagedTypes.IsNativePointer(plan.Leaves[0].Projection.Type))
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "令牌句柄布局不是单个运行时指针", code: "lowering.Struct.TokenLayout");
        var entity = valueNames is not null && context.Get(valueNames, plan.Leaves[0].Value) is { IsSuccess: true } named
            ? (named.Value.Name as EntityName)?.Entity : null;
        if (type.Equals(types.RuntimeTypeHandle) && (entity is TypeEntity or ClassEntity))
        {
            var target = entity is TypeEntity definition ? definition.Type : ((ClassEntity)entity).Type;
            if (!ManagedAccess.Type(types, method.Method.Owner, target))
                return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "令牌的目标类型不可访问：" + target, code: "lowering.Struct.TokenAccess");
            return new TypeHandleValue(target, type, 0);
        }
        if (type.Equals(types.RuntimeFieldHandle) && entity is FieldEntity field) return new FieldHandleValue(field.Field, type, 0);
        if (type.Equals(types.RuntimeMethodHandle) && entity is MethodEntity called) return new MethodHandleValue(called.Method, type, 0);
        return entity is null ? null : Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
            "令牌句柄的实体种类与句柄类型不符", code: "lowering.Struct.TokenEntity");
    }
}
