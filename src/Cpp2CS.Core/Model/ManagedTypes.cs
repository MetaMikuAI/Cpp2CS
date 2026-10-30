using System.Reflection;

namespace Cpp2CS.Model;

/// <summary>托管值在 IL 求值栈上的类别。</summary>
public enum TypeKind { Void, Bool, Int, Float, Double, Reference, Pointer, Struct }

/// <summary>字段访问：字段与按接收者实参代入后的字段类型。</summary>
public sealed record FieldAccess(FieldRef Field, TypeRef Type);

/// <summary>
/// L3 使用的托管类型视图：基元宽度与符号、枚举底层类型、可赋值关系，以及按运行时布局（<see cref="ITypeLayouts"/>）把访存偏移解释为字段。
/// </summary>
public sealed class ManagedTypes
{
    private readonly Dictionary<string, TypeDef> corlib = new();

    public ManagedTypes(ProgramModel model, ITypeLayouts layouts)
    {
        Model = model;
        Layouts = layouts;
        foreach (var type in model.Types.Where(t => t.Assembly == "mscorlib.dll" && t.DeclaringType is null)) corlib.TryAdd(type.FullName, type);
        Object = Corlib("System.Object");
        String = Corlib("System.String");
        Boolean = Corlib("System.Boolean");
        Char = Corlib("System.Char");
        SByte = Corlib("System.SByte");
        Byte = Corlib("System.Byte");
        Int16 = Corlib("System.Int16");
        UInt16 = Corlib("System.UInt16");
        Int32 = Corlib("System.Int32");
        UInt32 = Corlib("System.UInt32");
        Int64 = Corlib("System.Int64");
        UInt64 = Corlib("System.UInt64");
        Single = Corlib("System.Single");
        Double = Corlib("System.Double");
        IntPtr = Corlib("System.IntPtr");
        RuntimeTypeHandle = Corlib("System.RuntimeTypeHandle");
    }

    public ProgramModel Model { get; }
    public ITypeLayouts Layouts { get; }
    public DefinitionRef Object { get; }
    public DefinitionRef String { get; }
    public DefinitionRef Boolean { get; }
    public DefinitionRef Char { get; }
    public DefinitionRef SByte { get; }
    public DefinitionRef Byte { get; }
    public DefinitionRef Int16 { get; }
    public DefinitionRef UInt16 { get; }
    public DefinitionRef Int32 { get; }
    public DefinitionRef UInt32 { get; }
    public DefinitionRef Int64 { get; }
    public DefinitionRef UInt64 { get; }
    public DefinitionRef Single { get; }
    public DefinitionRef Double { get; }
    public DefinitionRef IntPtr { get; }
    public DefinitionRef RuntimeTypeHandle { get; }

    public DefinitionRef Corlib(string fullName) => new(corlib[fullName], []);
    public TypeDef? CorlibDefinition(string fullName) => corlib.GetValueOrDefault(fullName);

    /// <summary>IL2CPP 共享实参：引用归为 object，枚举归为同底层类型的共享枚举，值类型实参递归处理。</summary>
    public TypeRef SharedGenericArgument(TypeRef type) => IsReferenceType(type) ? Object : type switch
    {
        DefinitionRef { Definition.IsEnum: true } e when CorlibDefinition($"System.{PrimitiveName(Underlying(e))}Enum") is { IsEnum: true } shared
            && Underlying(new DefinitionRef(shared, [])).Equals(Underlying(e)) => new DefinitionRef(shared, []),
        DefinitionRef { Arguments.Count: > 0 } value => value with { Arguments = value.Arguments.Select(SharedGenericArgument).ToArray() },
        _ => type,
    };

    /// <summary>mscorlib 中 owner 类型名为 name、参数类型依次为 parameters 的方法；没有时为 null。</summary>
    public MethodRef? CorlibMethod(string owner, string name, params TypeRef[] parameters) =>
        CorlibDefinition(owner)?.Methods.FirstOrDefault(m => m.Name == name && m.GenericParameters.Count == 0
            && m.Parameters.Select(p => p.Type).SequenceEqual(parameters)) is { } method ? new MethodRef(method, [], []) : null;

    /// <summary>System 命名空间的基元类型名（Int32、Boolean……），其他为 null。</summary>
    public static string? PrimitiveName(TypeRef type) => type is DefinitionRef { Definition: { Namespace: "System", DeclaringType: null, Assembly: "mscorlib.dll" } d, Arguments.Count: 0 }
        && d.Name is "Boolean" or "Char" or "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64"
            or "Single" or "Double" or "IntPtr" or "UIntPtr" or "Void"
        ? d.Name : null;

    public static bool IsVoid(TypeRef type) => type is PrimitiveRef { Name: "void" } || PrimitiveName(type) == "Void";

    /// <summary>非托管指针值与原生整数；不包含需要保持 GC 跟踪的托管引用地址。</summary>
    public static bool IsNativePointer(TypeRef type) => type is PointerRef || PrimitiveName(type) is "IntPtr" or "UIntPtr";

    /// <summary>枚举的底层整数类型；非枚举原样返回。</summary>
    public static TypeRef Underlying(TypeRef type) =>
        type is DefinitionRef { Definition: { IsEnum: true } definition } ? definition.Fields.First(f => !f.IsStatic).Type : type;

    public static bool IsReferenceType(TypeRef type) => type switch
    {
        ArrayRef => true,
        GenericParameterRef generic => generic.IsReference,
        DefinitionRef d => !d.Definition.IsValueType,
        _ => false,
    };

    /// <summary>值的类别；泛型参数（共享代码）为 null。</summary>
    public TypeKind? Kind(TypeRef type)
    {
        if (IsVoid(type)) return TypeKind.Void;
        type = Underlying(type);
        switch (type)
        {
            case ArrayRef: return TypeKind.Reference;
            case GenericParameterRef { IsReference: true }: return TypeKind.Reference;
            case GenericParameterRef { NativeScalar: { } scalar }: return Kind(scalar);
            case GenericParameterRef { NativeAggregate: not null }: return TypeKind.Struct;
            case PointerRef or ByRefRef: return TypeKind.Pointer;
            case DefinitionRef d:
                if (SharedTypes.IsFullyShared(d) && d.Definition.IsValueType) return null;
                return PrimitiveName(d) switch
                {
                    "Boolean" => TypeKind.Bool,
                    "Single" => TypeKind.Float,
                    "Double" => TypeKind.Double,
                    "IntPtr" or "UIntPtr" => TypeKind.Pointer,
                    "Char" or "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64" => TypeKind.Int,
                    _ => d.Definition.IsValueType ? TypeKind.Struct : TypeKind.Reference,
                };
            default: return null;
        }
    }

    /// <summary>值的字节数（结构体为实例数据大小）；无法确定为 -1。</summary>
    public int Size(TypeRef type) => Layouts.TrySizeAndAlignment(type)?.Size ?? -1;

    /// <summary>非结构体值在机器上的位宽（bool 为 8）。</summary>
    public int Bits(TypeRef type) => Kind(type) is TypeKind.Struct or null ? -1 : Size(type) * 8;

    public static bool IsSigned(TypeRef type) => PrimitiveName(Underlying(type)) is "SByte" or "Int16" or "Int32" or "Int64" or "IntPtr";

    public DefinitionRef Integer(int bits, bool signed) => bits switch
    {
        8 => signed ? SByte : Byte,
        16 => signed ? Int16 : UInt16,
        32 => signed ? Int32 : UInt32,
        64 => signed ? Int64 : UInt64,
        _ => throw new ArgumentOutOfRangeException(nameof(bits), bits, "整数位宽"),
    };

    /// <summary>from 的值能否不经转换赋给 to；按元数据处理继承、接口及引用实参的泛型变体。</summary>
    public bool IsAssignable(TypeRef from, TypeRef to)
    {
        if (from.Equals(to)) return true;
        if (!IsReferenceType(from) || !IsReferenceType(to)) return false;
        if (to.Equals(Object)) return true;
        if (from is GenericParameterRef generic)
            return generic.Parameter?.Constraints.Any(c => IsAssignable(c, to)) == true;
        if (from is ArrayRef array)
        {
            // C# 17.2.2/17.2.3、17.6：数组继承 Array；只有 SZARRAY 实现泛型集合接口。
            // 元素协变只允许引用转换，不能把值类型数组当作装箱后的数组。
            if (to is ArrayRef targetArray)
                return array.Rank == targetArray.Rank && array.IsVector == targetArray.IsVector
                    && IsReferenceType(array.Element) && IsReferenceType(targetArray.Element)
                    && IsAssignable(array.Element, targetArray.Element);
            if (array is { Rank: 1, IsVector: true } && to is DefinitionRef
                {
                    Definition:
                    {
                        Assembly: "mscorlib.dll", Namespace: "System.Collections.Generic", DeclaringType: null,
                        Name: "IEnumerable`1" or "ICollection`1" or "IList`1" or "IReadOnlyCollection`1" or "IReadOnlyList`1", IsInterface: true
                    }, Arguments: [var element]
                }
                && (array.Element.Equals(element) || IsReferenceType(array.Element) && IsReferenceType(element) && IsAssignable(array.Element, element))) return true;
            return CorlibDefinition("System.Array") is { } definition && IsAssignable(new DefinitionRef(definition, []), to);
        }
        for (TypeRef? current = from; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
        {
            if (current.Equals(to) || to is DefinitionRef target && VariantAssignable(c, target)) return true;
            foreach (var itf in c.Definition.Interfaces)
                if (Implements(itf.Substitute(c.Arguments, []), to)) return true;
        }
        return false;
    }

    private bool Implements(TypeRef itf, TypeRef target) =>
        itf.Equals(target) || itf is DefinitionRef d && (target is DefinitionRef t && VariantAssignable(d, t)
            || d.Definition.Interfaces.Any(i => Implements(i.Substitute(d.Arguments, []), target)));

    private bool VariantAssignable(DefinitionRef from, DefinitionRef to)
    {
        if (from.Definition != to.Definition || from.Arguments.Count == 0 || from.Arguments.Count != to.Arguments.Count
            || from.Definition.GenericParameters.Count != from.Arguments.Count
            || !from.Definition.IsInterface && from.Definition.BaseType is not
                DefinitionRef { Definition: { Assembly: "mscorlib.dll", FullName: "System.MulticastDelegate" } }) return false;
        for (var i = 0; i < from.Arguments.Count; i++)
        {
            var source = from.Arguments[i];
            var target = to.Arguments[i];
            if (source.Equals(target)) continue;
            if (!IsReferenceType(source) || !IsReferenceType(target)) return false;
            var matches = (from.Definition.GenericParameters[i].Attributes & GenericParameterAttributes.VarianceMask) switch
            {
                GenericParameterAttributes.Covariant => IsAssignable(source, target),
                GenericParameterAttributes.Contravariant => IsAssignable(target, source),
                _ => false,
            };
            if (!matches) return false;
        }
        return true;
    }

    /// <summary>
    /// 接收者 receiver（引用类型的对象，或值类型数据的指针 ByRefRef）中起始于 offset、宽 bytes 字节的字段。
    /// offset 相对接收者指针：引用类型含对象头，值类型指针不含。沿基类链查找；只接受与字段完全重合的访问。
    /// </summary>
    public FieldAccess? InstanceField(TypeRef receiver, int offset, int bytes)
    {
        TypeRef? current = receiver;
        if (receiver is GenericParameterRef { ReferenceBase: { } constraint }) current = constraint;
        if (receiver is ByRefRef { Element: DefinitionRef { Definition.IsValueType: true } value })
        {
            current = value;
            offset += TypeLayout.ObjectHeaderSize;
        }
        else if (!IsReferenceType(receiver) || receiver is ArrayRef) return null;
        for (; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
        {
            if (Layouts.Of(c) is not { } layout) return null;
            foreach (var slot in layout.Fields)
                if (slot.Offset == offset && Size(slot.Type) == bytes) return new(new FieldRef(slot.Field, c), slot.Type.Substitute(c.Arguments, []));
            if (c.Definition.IsValueType) break;
        }
        return null;
    }

    /// <summary>类型静态字段块中起始于 offset、宽 bytes 字节的字段。</summary>
    public FieldAccess? StaticField(DefinitionRef owner, int offset, int bytes)
    {
        if (Layouts.Of(owner) is not { } layout) return null;
        foreach (var slot in layout.Statics)
            // 泛型类型封闭实例的静态字段：字段类型代入类型实参（如 EmptyArray<X>.Value 是 X[]）。
            if (slot.Offset == offset && Size(slot.Type) == bytes) return new(new FieldRef(slot.Field, owner), slot.Type.Substitute(owner.Arguments, []));
        return null;
    }
}
