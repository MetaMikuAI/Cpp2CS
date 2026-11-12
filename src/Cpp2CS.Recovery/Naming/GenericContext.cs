using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Naming;

/// <summary>装配处按定义所属的 RGCTX 区间解码，不把见证中的 object 反代入。</summary>
public interface IRgctxDecoder
{
    Outcome<MetadataEntity> Decode(MethodRef definition, bool methodContext, int index);
}

public sealed partial class ValueNamingQuery
{
    internal GenericWitness? Witness => witness;
    internal MethodRef? DefinitionMethod => witness?.Definition;
    private SharedCallQuery? sharedResults;

    internal bool ContextEntity(ValueName? name) => witness is not null && (name switch
    {
        ParameterName { MethodInformation: true } => true,
        EntityName { Entity: ClassEntity type } => type.Type.ContainsGenericParameter() && witness.Knows(type.Type),
        EntityName { Entity: MethodEntity method } => method.Method.TypeArguments.Concat(method.Method.MethodArguments)
            .Any(t => t.ContainsGenericParameter()) && witness.Knows(method.Method),
        _ => false,
    });

    private static NamedValue Entity(MetadataEntity entity, ulong slot = 0)
    {
        var name = new EntityName(entity, slot);
        return entity switch
        {
            ClassEntity => new(ValueKind.RuntimePointer, name, "Il2CppClass"),
            TypeEntity => new(ValueKind.RuntimePointer, name, "Il2CppType"),
            MethodEntity => new(ValueKind.RuntimePointer, name, "MethodInfo"),
            FieldEntity => new(ValueKind.RuntimePointer, name, "FieldInfo"),
            StringEntity => new(ValueKind.ManagedReference, name, "Il2CppString"),
            _ => NamedValue.Unknown("naming.entity", "未登记的实体种类。")
        };
    }

    private Outcome<NamedValue>? ContextRead(Location location, int low, ValueName parent, string record)
    {
        if (witness is null || low != 0 || location.Width != spec.Layout.Record("Il2CppRGCTXData").Size * 8) return null;
        var definition = witness.Definition;
        if (record == "MethodInfo" && parent is ParameterName { MethodInformation: true })
        {
            if (location.Offset == spec.Layout.Field("MethodInfo", "klass").ByteOffset)
                return Yes(Entity(new ClassEntity(definition.DeclaringType)));
            // il2cpp-class-internals.h：泛型方法实例的联合成员是 rgctx_data。
            if (definition.Method.GenericParameters.Count > 0 && location.Offset == spec.Layout.Field("MethodInfo", "rgctx_data").ByteOffset)
                return Yes(Field(parent, record, spec.Layout.Field("MethodInfo", "rgctx_data")));
        }
        if (record != "Il2CppRGCTXData" || rgctx is null) return null;
        bool methodContext;
        if (parent is FieldName { Record: "MethodInfo", Field: "MethodInfo.rgctx_data", Owner: ParameterName { MethodInformation: true } }
            && definition.Method.GenericParameters.Count > 0) methodContext = true;
        else if (parent is FieldName { Record: "Il2CppClass", Field: "Il2CppClass.rgctx_data", Owner: EntityName { Entity: ClassEntity owner } }
            && owner.Type == definition.DeclaringType && definition.Method.Owner.GenericParameters.Count > 0
            && definition.Method.GenericParameters.Count == 0) methodContext = false;
        else return null;
        var size = spec.Layout.Record("Il2CppRGCTXData").Size;
        if (location.Offset is not { } offset || offset < 0 || offset % size != 0 || offset / size > int.MaxValue)
            return Yes(NamedValue.Unknown("naming.rgctx-index", "泛型上下文访问不是一个完整的定值索引项。"));
        var decoded = rgctx.Decode(definition, methodContext, (int)(offset / size));
        if (!decoded.IsSuccess) return Yes(new(ValueKind.Unnamed, null, Why: decoded.Why));
        bool known = decoded.Value switch
        {
            ClassEntity type => witness.Knows(type.Type), TypeEntity type => witness.Knows(type.Type),
            MethodEntity method => witness.Knows(method.Method), _ => false,
        };
        return Yes(known ? Entity(decoded.Value) : NamedValue.Unknown("naming.rgctx-scope", "泛型上下文实体含有本定义之外的开放类型。"));
    }
}
