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
    public EntityRef SystemObject => metadata.TypeEntity(metadata.CoreType("Object"));
    private long variantInterfaceRejections, arrayInterfaceRejections;
    public long VariantInterfaceRejections => Interlocked.Read(ref variantInterfaceRejections);
    public long ArrayInterfaceRejections => Interlocked.Read(ref arrayInterfaceRejections);

    public MethodShape Method(EntityRef entity) => metadata.Method(entity);
    public FieldShape Field(EntityRef entity) => metadata.Field(entity);
    public TypeShape Type(EntityRef entity) => metadata.Type(entity);

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
        if (metadata.Keys.DescribeType(from) is not NamedType host) return false;
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

    public EntityRef? DeclaringTypeOf(EntityRef method)
    {
        if (metadata.Keys.DescribeMethod(method) is not { } instance) return null;
        var owner = new NamedType(Model.Methods[instance.Definition].Owner, instance.TypeArguments);
        return metadata.Keys.TypeKey(owner) is long key ? new EntityRef(EntityKind.Type, key) : null;
    }

    public bool? IsInstanceConstructor(EntityRef method)
    {
        if (metadata.Keys.DescribeMethod(method) is not { } instance) return null;
        var definition = Model.Methods[instance.Definition];
        return definition.Name == ".ctor" && definition.Flags.HasFlag(MethodAttributes.RTSpecialName) && !definition.Flags.HasFlag(MethodAttributes.Static);
    }

    public bool? IsVirtual(EntityRef method) => metadata.Keys.DescribeMethod(method) is { } instance
        ? Model.Methods[instance.Definition].Flags.HasFlag(MethodAttributes.Virtual) : null;

    /// <summary>声明在给定类型上的实例构造函数。只有形参数量相符、可确定栈宽的签名能用于发现。</summary>
    public IEnumerable<MethodShape> InstanceConstructors(EntityRef type, int argumentCount)
    {
        if (metadata.Keys.DescribeType(type) is not NamedType owner) yield break;
        var declaration = Model.Types[owner.Definition];
        for (int i = declaration.FirstMethod; i < declaration.FirstMethod + declaration.MethodCount; i++)
        {
            if (Model.Methods[i].Parameters.Count + 1 != argumentCount) continue;
            if (IsInstanceConstructor(new(EntityKind.Method, i)) != true) continue;
            long? key = owner.Arguments.Count == 0 ? i : metadata.Keys.MethodKey(new MethodInstance(i, owner.Arguments, []));
            if (key is null) continue;
            MethodShape shape;
            try { shape = metadata.Method(new(EntityKind.Method, key.Value)); }
            catch (ExpansionException e) when (e.Reason == "元数据事实不足") { continue; }
            yield return shape;
        }
    }

    public bool? IsValueType(EntityRef type) => metadata.Keys.DescribeType(type) switch
    {
        null => null,
        NamedType named => Model.Types[named.Definition].ValueType,
        _ => false,
    };

    public EntityRef? BaseOf(EntityRef type)
    {
        // 泛型实例的基类是定义里写的基类代入这个实例的类型实参（ECMA-335 II.9.4）。
        if (metadata.Keys.DescribeType(type) is not NamedType named) return null;
        if (Model.Types[named.Definition].Parent is not { } declared) return null;
        if (EntityKeys.Inflate(declared, named) is not NamedType parent || metadata.Keys.TypeKey(parent) is not long key) return null;
        return new EntityRef(EntityKind.Type, key);
    }

    public bool Assignable(EntityRef from, EntityRef to) =>
        metadata.Keys.DescribeType(from) is { } source && metadata.Keys.DescribeType(to) is { } destination
        && Assignable(source, destination);

    /// <summary>按本模型的签名判定；基类与接口代入后可以没有单独的运行时类型键。</summary>
    public bool Assignable(TypeReference source, TypeReference destination)
    {
        if (!KnownSignature(source) || !KnownSignature(destination)) return false;
        if (destination is not NamedType target) return EntityKeys.Structure(source) == EntityKeys.Structure(destination);
        var targetType = Model.Types[target.Definition];
        bool isInterface = targetType.Flags.HasFlag(TypeAttributes.Interface);
        bool genericInterface = isInterface && target.Arguments.Count > 0;
        bool isObject = metadata.IsCore(target.Definition, "Object");
        // ECMA-335 I.8.9.1、I.8.7.1：数组以 System.Array 为基类。向量的泛型接口另有相容规则。
        if (source is ArrayType)
        {
            if (genericInterface) Interlocked.Increment(ref arrayInterfaceRejections);
            return isObject || metadata.IsCore(target.Definition, "Array");
        }
        if (source is not NamedType named) return false;
        // I.8.7.1 第 1 条：相同签名直接相容，不涉及泛型实参的协变或逆变。
        if (named.Definition == target.Definition && EntityKeys.Structure(named) == EntityKeys.Structure(target)) return true;
        // ECMA-335 II.9.5：带变体形参的接口由独立的规则判定。
        if (genericInterface && targetType.GenericParameters.Any(p => (p.Flags & GenericParameterAttributes.VarianceMask) != 0))
        {
            Interlocked.Increment(ref variantInterfaceRejections);
            return false;
        }
        if (Model.Types[named.Definition].ValueType) return false;
        return isObject || HasSupertype(named, target, isInterface, []);
    }

    // II.9.4：具名类型的实参数须与定义一致。按引用类型不是合法的泛型实参，不能用去掉按引用标记的实体键作证。
    private bool KnownSignature(TypeReference type) => type switch
    {
        NamedType n => (uint)n.Definition < Model.Types.Count && n.Arguments.Count == Model.Types[n.Definition].GenericParameters.Count
            && n.Arguments.All(a => a is not PointerType && KnownSignature(a)),
        ArrayType a => a.Rank > 0 && (!a.Vector || a.Rank == 1) && KnownSignature(a.Element),
        PointerType p => KnownSignature(p.Element),
        VariableType v when v.Method => (uint)v.Owner < Model.Methods.Count && (uint)v.Position < Model.Methods[v.Owner].GenericParameters.Count,
        VariableType v => (uint)v.Owner < Model.Types.Count && (uint)v.Position < Model.Types[v.Owner].GenericParameters.Count,
        _ => false,
    };

    // ECMA-335 I.8.7.1、II.9.4：各层基类和接口用当前实例的实参代入，不变类型要求定义和每个实参都相同。
    private bool HasSupertype(NamedType current, NamedType target, bool interfaces, HashSet<int> path)
    {
        if (!KnownSignature(current) || !path.Add(current.Definition)) return false;
        var definition = Model.Types[current.Definition];
        bool matches = current.Definition == target.Definition
            && (target.Arguments.Count == 0 || EntityKeys.Structure(current) == EntityKeys.Structure(target))
            || Matches(definition.Parent) || interfaces && definition.Interfaces.Any(Implemented);
        path.Remove(current.Definition);
        return matches;

        bool Matches(TypeReference? declared) => declared is NamedType named && EntityKeys.Inflate(named, current) is NamedType next
            && HasSupertype(next, target, interfaces, path);

        bool Implemented(TypeReference declared) => target.Arguments.Count == 0
            ? declared is NamedType { Arguments.Count: 0 } direct && direct.Definition == target.Definition
            : Matches(declared);
    }

    public TypeShape? ElementOf(EntityRef array)
    {
        if (metadata.Keys.DescribeType(array) is not ArrayType { Vector: true } vector) return null;
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
        for (var at = metadata.Keys.DescribeType(type) as NamedType; at is not null; )
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

    public FieldShape? StaticFieldAt(EntityRef type, int offset)
    {
        if (metadata.Keys.DescribeType(type) is not NamedType owner) return null;
        var definition = Model.Types[owner.Definition];
        for (int i = definition.FirstField; i < definition.FirstField + definition.FieldCount; i++)
        {
            if (Model.Fields[i].Storage != FieldStorage.Static) continue;
            try
            {
                if (metadata.FieldOffset(i, owner, FieldStorage.Static) == offset && metadata.Keys.FieldKey(i, owner) is long key)
                    return metadata.Field(new EntityRef(EntityKind.Field, key));
            }
            catch (ExpansionException)
            {
                // 这个字段的静态区偏移没有依据：不作候选。
            }
        }
        return null;
    }
}
