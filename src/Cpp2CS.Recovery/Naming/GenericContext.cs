using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Naming;

/// <summary>按实体所属的 RGCTX 区间与自己的实参解码，不把见证中的 object 反代入。</summary>
public interface IRgctxDecoder
{
    Outcome<MetadataEntity> Decode(MethodRef method, bool methodContext, int index);
    Outcome<MetadataEntity> Decode(DefinitionRef type, int index);
}

public sealed partial class ValueNamingQuery
{
    internal GenericWitness? Witness => witness;
    internal MethodRef? DefinitionMethod => witness?.Definition;
    private SharedCallQuery? sharedResults;

    internal bool ContextEntity(ValueName? name) => name switch
    {
        ParameterName { MethodInformation: true } => witness is not null,
        EntityName { Entity: ClassEntity type } => Known(type.Type),
        EntityName { Entity: MethodEntity method } => Known(method.Method),
        _ => false,
    };

    private bool Known(TypeRef type) => witness?.Knows(type) ?? Cpp2CS.Runtime.ManagedCSignatureBuilder.IsClosed(type);
    private bool Known(MethodRef method) => witness?.Knows(method) ?? Cpp2CS.Runtime.ManagedCSignatureBuilder.IsClosed(method);
    private MethodRef? ContextMethod(ValueName parent) => parent switch
    {
        ParameterName { MethodInformation: true } => witness?.Definition,
        EntityName { Entity: MethodEntity method } when Known(method.Method) => method.Method,
        _ => null,
    };

    private NamedValue Entity(MetadataEntity entity, ulong slot = 0)
    {
        var name = new EntityName(entity, slot);
        return entity switch
        {
            ClassEntity => new(ValueKind.RuntimePointer, name, "Il2CppClass"),
            TypeEntity => new(ValueKind.RuntimePointer, name, "Il2CppType"),
            MethodEntity => new(ValueKind.RuntimePointer, name, "MethodInfo"),
            FieldEntity => new(ValueKind.RuntimePointer, name, "FieldInfo"),
            StringEntity => new(ValueKind.ManagedReference, name, "Il2CppString") { ReferenceType = stringType },
            _ => NamedValue.Unknown("naming.entity", "未登记的实体种类。")
        };
    }

    private Outcome<NamedValue>? ContextRead(Location location, int low, ValueName parent, string record)
    {
        if (low != 0 || location.Width != spec.Layout.Record("Il2CppRGCTXData").Size * 8) return null;
        if (record == "MethodInfo" && ContextMethod(parent) is { } definition)
        {
            if (location.Offset == spec.Layout.Field("MethodInfo", "klass").ByteOffset)
                return Yes(Entity(new ClassEntity(definition.DeclaringType)));
            // il2cpp-class-internals.h：泛型方法实例的联合成员是 rgctx_data。
            if (definition.Method.GenericParameters.Count > 0 && location.Offset == spec.Layout.Field("MethodInfo", "rgctx_data").ByteOffset)
                return Yes(Field(parent, record, spec.Layout.Field("MethodInfo", "rgctx_data")));
        }
        if (record != "Il2CppRGCTXData" || rgctx is null) return null;
        MethodRef? method = null;
        DefinitionRef? type = null;
        if (parent is FieldName { Record: "MethodInfo", Field: "MethodInfo.rgctx_data", Owner: var information }
            && ContextMethod(information) is { Method.GenericParameters.Count: > 0 } ownerMethod) method = ownerMethod;
        else if (parent is FieldName { Record: "Il2CppClass", Field: "Il2CppClass.rgctx_data", Owner: EntityName { Entity: ClassEntity { Type: DefinitionRef ownerType } } }
            && ownerType.Definition.GenericParameters.Count > 0 && Known(ownerType)) type = ownerType;
        else return null;
        var size = spec.Layout.Record("Il2CppRGCTXData").Size;
        if (location.Offset is not { } offset || offset < 0 || offset % size != 0 || offset / size > int.MaxValue)
            return Yes(NamedValue.Unknown("naming.rgctx-index", "泛型上下文访问不是一个完整的定值索引项。"));
        var decoded = method is not null ? rgctx.Decode(method, true, (int)(offset / size)) : rgctx.Decode(type!, (int)(offset / size));
        if (!decoded.IsSuccess) return Yes(new(ValueKind.Unnamed, null, Why: decoded.Why));
        bool known = decoded.Value switch
        {
            ClassEntity klass => Known(klass.Type), TypeEntity handle => Known(handle.Type),
            MethodEntity target => Known(target.Method), _ => false,
        };
        return Yes(known ? Entity(decoded.Value) : NamedValue.Unknown("naming.rgctx-scope", "泛型上下文实体含有本定义之外的开放类型或不完整实参。"));
    }
}
