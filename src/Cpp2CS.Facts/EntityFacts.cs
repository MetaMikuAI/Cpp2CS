using System.Reflection;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Model;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Facts;

/// <summary>
/// 解释层按实体提问的元数据（设计第 8 节），在元数据模型上实现。形状转交给 <see cref="ModelMetadata"/>；
/// 这里回答可访问性（ECMA-335 I.8.5.3）、赋值相容（I.8.7 里类、接口与基类的部分）、数组元素类型与按偏移找字段。
/// </summary>
public sealed class EntityFacts(ModelMetadata metadata) : IEntityMetadata
{
    private MetadataModel Model => metadata.Model;

    public MethodShape Method(EntityRef entity) => metadata.Method(entity);
    public FieldShape Field(EntityRef entity) => metadata.Field(entity);
    public TypeShape Type(EntityRef entity) => metadata.Type(entity);

    private TypeReference? Reference(EntityRef type) =>
        type.Kind == EntityKind.Type && type.Key >= 0 && type.Key < Model.RuntimeTypes.Count
            ? Model.RuntimeTypes[(int)type.Key] is ReferenceType reference ? reference.Element : Model.RuntimeTypes[(int)type.Key] : null;

    private int ImageOf(int definition)
    {
        for (int i = 0; i < Model.Images.Count; i++)
            if (definition >= Model.Images[i].FirstType && definition < Model.Images[i].FirstType + Model.Images[i].TypeCount) return i;
        return -1;
    }

    /// <summary>from 是 owner 自己，或嵌套在 owner 之内。</summary>
    private bool Within(int from, int owner)
    {
        for (int? at = from; at is int current; at = Model.Types[current].DeclaringType)
            if (current == owner) return true;
        return false;
    }

    private bool Derives(int from, int ancestor)
    {
        for (int? at = from; at is int current; at = Model.Types[current].Parent is NamedType parent ? parent.Definition : null)
            if (current == ancestor) return true;
        return false;
    }

    /// <summary>from 或包住它的某个类，是 owner 或派生自 owner。</summary>
    private bool Family(int from, int owner)
    {
        for (int? at = from; at is int current; at = Model.Types[current].DeclaringType)
            if (Derives(current, owner)) return true;
        return false;
    }

    private bool TypeVisible(int definition, int from)
    {
        var type = Model.Types[definition];
        bool assembly = ImageOf(definition) == ImageOf(from);
        if (type.DeclaringType is not int outer)
            return (type.Flags & TypeAttributes.VisibilityMask) == TypeAttributes.Public || assembly;
        if (!TypeVisible(outer, from)) return false;
        return (type.Flags & TypeAttributes.VisibilityMask) switch
        {
            TypeAttributes.NestedPublic => true,
            TypeAttributes.NestedPrivate => Within(from, outer),
            TypeAttributes.NestedFamily => Within(from, outer) || Family(from, outer),
            TypeAttributes.NestedAssembly => assembly,
            TypeAttributes.NestedFamORAssem => assembly || Family(from, outer),
            TypeAttributes.NestedFamANDAssem => assembly && Family(from, outer),
            _ => false,
        };
    }

    public bool Accessible(EntityRef member, EntityRef from)
    {
        if (Reference(from) is not NamedType host) return false;
        int owner;
        int access;
        if (member.Kind == EntityKind.Field && metadata.Keys.DescribeField(member) is { } field)
        {
            owner = field.Owner.Definition;
            access = (int)(Model.Fields[field.Index].Flags & FieldAttributes.FieldAccessMask);
        }
        else if (member.Kind == EntityKind.Method && metadata.Keys.DescribeMethod(member) is { } method)
        {
            owner = Model.Methods[method.Definition].Owner;
            access = (int)(Model.Methods[method.Definition].Flags & MethodAttributes.MemberAccessMask);
        }
        else return false;
        if (!TypeVisible(owner, host.Definition)) return false;
        bool assembly = ImageOf(owner) == ImageOf(host.Definition);
        // 字段与方法的访问级别取值相同（ECMA-335 II.23.1.5、II.23.1.10）。
        return (FieldAttributes)access switch
        {
            FieldAttributes.Public => true,
            FieldAttributes.Private or FieldAttributes.PrivateScope => Within(host.Definition, owner),
            FieldAttributes.Family => Within(host.Definition, owner) || Family(host.Definition, owner),
            FieldAttributes.Assembly => assembly,
            FieldAttributes.FamORAssem => assembly || Family(host.Definition, owner),
            FieldAttributes.FamANDAssem => assembly && Family(host.Definition, owner),
            _ => false,
        };
    }

    public bool Assignable(EntityRef from, EntityRef to)
    {
        if (from == to) return true;
        if (Reference(from) is not { } source || Reference(to) is not NamedType target) return false;
        var targetType = Model.Types[target.Definition];
        bool isObject = targetType.Parent is null && !targetType.Flags.HasFlag(TypeAttributes.Interface);
        if (source is ArrayType) return isObject;
        if (source is not NamedType named || Model.Types[named.Definition].ValueType) return false;
        if (isObject) return true;
        if (target.Arguments.Count > 0) return false;
        for (int? at = named.Definition; at is int current; at = Model.Types[current].Parent is NamedType parent ? parent.Definition : null)
        {
            if (current == target.Definition) return true;
            foreach (var implemented in Model.Types[current].Interfaces)
                if (implemented is NamedType { Arguments.Count: 0 } iface && iface.Definition == target.Definition) return true;
        }
        return false;
    }

    public TypeShape? ElementOf(EntityRef array)
    {
        if (Reference(array) is not ArrayType { Vector: true } vector) return null;
        try
        {
            return metadata.Shape(vector.Element);
        }
        catch (ExpansionException)
        {
            return null;
        }
    }

    public FieldShape? FieldAt(EntityRef type, int offset)
    {
        for (var at = Reference(type) as NamedType; at is not null; )
        {
            var definition = Model.Types[at.Definition];
            for (int i = definition.FirstField; i < definition.FirstField + definition.FieldCount; i++)
            {
                if (Model.Fields[i].Storage != FieldStorage.Instance) continue;
                try
                {
                    if (metadata.FieldOffset(i, at, FieldStorage.Instance) == offset && metadata.Keys.FieldKey(i, at) is long key)
                        return metadata.Field(new EntityRef(EntityKind.Field, key));
                }
                catch (ExpansionException)
                {
                    // 这个字段的布局没有依据：不作候选。
                }
            }
            // 基类：非泛型的基类按定义；泛型基类按所属类型的实参代入。
            at = definition.Parent is NamedType parent ? EntityKeys.Inflate(parent, at) as NamedType : null;
        }
        return null;
    }
}
