using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>托管值在机器上的类别（决定寄存器组、宽度与 IL 栈类型）。</summary>
public enum ValueKind { Void, Bool, Int, Float, Double, Reference, Pointer, Struct }

/// <summary>
/// 托管类型的机器视图：基元宽度与符号、枚举底层类型、对象头、实例字段布局。
/// 泛型值类型按实参计算字段位置，不能直接使用泛型定义的偏移。
/// </summary>
public sealed class ManagedTypes
{
    private readonly Dictionary<string, TypeDef> corlib = new();
    private readonly Dictionary<TypeDef, FieldDef[]> instanceFields = new();
    public ValueLayouts Layouts { get; } = new();

    public ManagedTypes(ProgramModel model, int headerSize)
    {
        Model = model;
        HeaderSize = headerSize;
        foreach (var type in model.Types.Where(t => t.Assembly == "mscorlib.dll" && t.DeclaringType is null)) corlib.TryAdd(type.FullName, type);
        Object = Corlib("System.Object");
        String = Corlib("System.String");
        Void = Corlib("System.Void");
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
        UIntPtr = Corlib("System.UIntPtr");
        Array = Corlib("System.Array");
        Type = Corlib("System.Type");
        Delegate = Corlib("System.Delegate");
        MulticastDelegate = Corlib("System.MulticastDelegate");
        RuntimeTypeHandle = Corlib("System.RuntimeTypeHandle");
        RuntimeFieldHandle = Corlib("System.RuntimeFieldHandle");
    }

    public ProgramModel Model { get; }
    /// <summary>对象头字节数（vtable 指针 + monitor）。</summary>
    public int HeaderSize { get; }
    public DefinitionRef Object { get; }
    public DefinitionRef String { get; }
    public DefinitionRef Void { get; }
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
    public DefinitionRef UIntPtr { get; }
    public DefinitionRef Array { get; }
    public DefinitionRef Type { get; }
    public DefinitionRef Delegate { get; }
    public DefinitionRef MulticastDelegate { get; }
    public DefinitionRef RuntimeTypeHandle { get; }
    public DefinitionRef RuntimeFieldHandle { get; }

    public DefinitionRef Corlib(string fullName) => new(corlib[fullName], []);
    public TypeDef? CorlibDefinition(string fullName) => corlib.GetValueOrDefault(fullName);

    /// <summary>System 命名空间的基元类型名（Int32、Boolean……），其他为 null。</summary>
    public static string? PrimitiveName(TypeRef type) => type is DefinitionRef { Definition: { Namespace: "System", DeclaringType: null } d, Arguments.Count: 0 }
        && d.Name is "Boolean" or "Char" or "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64"
            or "Single" or "Double" or "IntPtr" or "UIntPtr" or "Void"
        ? d.Name : null;

    public static bool IsVoid(TypeRef type) => type is PrimitiveRef { Name: "void" } || PrimitiveName(type) == "Void";

    /// <summary>枚举的底层整数类型（value__ 字段的类型）；非枚举原样返回。</summary>
    public TypeRef Underlying(TypeRef type) =>
        type is DefinitionRef { Definition: { IsEnum: true } definition }
            ? definition.Fields.First(f => !f.IsStatic).Type
            : type;

    public static bool IsReferenceType(TypeRef type) => type switch
    {
        ArrayRef => true,
        DefinitionRef d => !d.Definition.IsValueType,
        _ => false,
    };

    public static bool IsClosed(TypeRef type) => type switch
    {
        DefinitionRef d => d.Arguments.Count == d.Definition.GenericParameters.Count && d.Arguments.All(IsClosed),
        ArrayRef a => IsClosed(a.Element),
        PointerRef p => IsClosed(p.Element),
        _ => false,
    };

    /// <summary>只有类型已闭合、布局已知且允许驻留堆上的值才可装箱。</summary>
    public bool CanBox(TypeRef type) => type is DefinitionRef { Definition.IsValueType: true } d
        && !IsVoid(type) && IsClosed(type) && Layouts.Get(type) is { Size: > 0 }
        && !d.Definition.CustomAttributes.Any(a => a.Constructor.Owner.FullName == "System.Runtime.CompilerServices.IsByRefLikeAttribute");

    /// <summary>值的类别。泛型参数无法确定（共享代码），返回 null。</summary>
    public ValueKind? Kind(TypeRef type)
    {
        if (IsVoid(type)) return ValueKind.Void;
        type = Underlying(type);
        switch (type)
        {
            case ArrayRef: return ValueKind.Reference;
            case PointerRef or ByRefRef or PrimitiveRef { Name: "nint" }: return ValueKind.Pointer;
            case GenericParameterRef: return null;
            case DefinitionRef d:
                return PrimitiveName(d) switch
                {
                    "Boolean" => ValueKind.Bool,
                    "Single" => ValueKind.Float,
                    "Double" => ValueKind.Double,
                    "IntPtr" or "UIntPtr" => ValueKind.Pointer,
                    "Char" or "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64" => ValueKind.Int,
                    _ => d.Definition.IsValueType ? ValueKind.Struct : ValueKind.Reference,
                };
            default: return null;
        }
    }

    /// <summary>非结构体值的字节宽度；结构体为实例数据大小（未知为 -1）；泛型参数为 -1。</summary>
    public int Size(TypeRef type)
    {
        type = Underlying(type);
        switch (Kind(type))
        {
            case ValueKind.Bool: return 1;
            case ValueKind.Float: return 4;
            case ValueKind.Double: return 8;
            case ValueKind.Reference or ValueKind.Pointer: return 8;
            case ValueKind.Int:
                return PrimitiveName(type) switch
                {
                    "SByte" or "Byte" => 1,
                    "Char" or "Int16" or "UInt16" => 2,
                    "Int32" or "UInt32" => 4,
                    _ => 8,
                };
            case ValueKind.Struct:
                var d = (DefinitionRef)type;
                return d.Arguments.Count == 0 ? d.Definition.Size : Layouts.Get(d)?.Size ?? -1;
            default: return -1;
        }
    }

    /// <summary>整数类型是否有符号（bool/char/byte/ushort/uint/ulong 为无符号）。</summary>
    public bool IsSigned(TypeRef type) => PrimitiveName(Underlying(type)) is "SByte" or "Int16" or "Int32" or "Int64" or "IntPtr";

    /// <summary>按位宽与符号选择整数类型。</summary>
    public DefinitionRef Integer(int bits, bool signed) => bits switch
    {
        8 => signed ? SByte : Byte,
        16 => signed ? Int16 : UInt16,
        32 => signed ? Int32 : UInt32,
        64 => signed ? Int64 : UInt64,
        _ => throw new ArgumentOutOfRangeException(nameof(bits), bits, "整数位宽"),
    };

    /// <summary>
    /// 实例字段（含基类，按偏移排序），字段类型按 type 的实参代入。
    /// 泛型值类型使用具体布局。泛型引用类型只保留全部实参为引用类型的共享布局路径（待验证）。
    /// </summary>
    public IReadOnlyList<InstanceField>? Fields(TypeRef type)
    {
        if (type is not DefinitionRef d) return null;
        if (d.Definition.IsValueType && d.Arguments.Count > 0) return Layouts.Get(d)?.Fields;
        if (d.Arguments.Count > 0 && !d.Arguments.All(IsReferenceType)) return null;
        var result = new List<InstanceField>();
        for (TypeRef? current = d; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
        {
            if (c.Arguments.Count > 0 && !c.Arguments.All(IsReferenceType)) return null;
            foreach (var field in Declared(c.Definition))
                result.Add(new InstanceField(new FieldRef(field, c), field.Type.Substitute(c.Arguments, []), field.Offset));
            if (c.Definition.IsValueType) break;
        }
        result.Sort((a, b) => a.Offset.CompareTo(b.Offset));
        return result;
    }

    private FieldDef[] Declared(TypeDef type)
    {
        if (!instanceFields.TryGetValue(type, out var fields))
            instanceFields[type] = fields = type.Fields.Where(f => !f.IsStatic && f.Offset >= 0).ToArray();
        return fields;
    }

    /// <summary>
    /// 在 type 的实例数据中找起始于 offset、宽度为 bytes 的字段（offset 相对对象起始：引用类型含对象头，值类型不含）。
    /// 结构体字段可继续向内查找，返回访问路径；找不到返回 null。
    /// </summary>
    public IReadOnlyList<(FieldRef Field, TypeRef Type)>? FieldPath(TypeRef type, int offset, int bytes)
    {
        var path = new List<(FieldRef, TypeRef)>();
        while (true)
        {
            if (Fields(type) is not { } fields) return null;
            InstanceField? hit = null;
            foreach (var f in fields)
            {
                var size = Size(f.Type);
                if (size <= 0) continue;
                if (offset >= f.Offset && offset < f.Offset + size)
                {
                    if (hit is not null) return null;
                    hit = f;
                }
            }
            if (hit is not { } found) return null;
            path.Add((found.Field, found.Type));
            var inner = offset - found.Offset;
            var fieldSize = Size(found.Type);
            if (inner == 0 && fieldSize == bytes) return path;
            if (Kind(found.Type) != ValueKind.Struct || inner + bytes > fieldSize) return null;
            type = found.Type;
            offset = inner;
        }
    }

    /// <summary>静态存储只包含本类字段；泛型静态布局、线程静态和未知偏移不套用普通静态字段布局。</summary>
    public IReadOnlyList<(FieldRef Field, TypeRef Type)>? StaticFieldPath(DefinitionRef owner, int offset, int bytes)
    {
        if (owner.Arguments.Count != 0 || owner.Definition.GenericParameters.Count != 0 || offset < 0 || bytes <= 0) return null;
        FieldDef? hit = null;
        foreach (var field in owner.Definition.Fields.Where(f => f.IsStatic && !f.IsThreadStatic && f.Offset >= 0
            && (f.Attributes & System.Reflection.FieldAttributes.Literal) == 0))
        {
            var size = Size(field.Type);
            if (size <= 0 || offset < field.Offset || (long)offset >= (long)field.Offset + size) continue;
            if (hit is not null) return null;
            hit = field;
        }
        if (hit is null) return null;
        var head = (new FieldRef(hit, owner), hit.Type);
        var inner = offset - hit.Offset;
        if (inner == 0 && Size(hit.Type) == bytes) return [head];
        if (Kind(hit.Type) != ValueKind.Struct || (long)inner + bytes > Size(hit.Type)
            || FieldPath(hit.Type, inner, bytes) is not { } nested) return null;
        return [head, .. nested];
    }

    /// <summary>a 是否可赋给 b（同一类型或 b 为 a 的基类/接口；引用类型）。</summary>
    public bool IsAssignable(TypeRef from, TypeRef to)
    {
        if (from.Equals(to)) return true;
        // 值类型到基类或接口需要显式装箱，不能仅沿元数据继承链当作引用赋值。
        if (!IsReferenceType(from) || !IsReferenceType(to)) return false;
        if (to.Equals(Object) && IsReferenceType(from)) return true;
        if (from is ArrayRef && to.Equals(Array)) return true;
        if (from is not DefinitionRef d) return false;
        for (TypeRef? current = d; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
        {
            if (current.Equals(to)) return true;
            foreach (var itf in c.Definition.Interfaces)
                if (Implements(itf.Substitute(c.Arguments, []), to)) return true;
        }
        return false;
    }

    private bool Implements(TypeRef itf, TypeRef target)
    {
        if (itf.Equals(target)) return true;
        if (itf is not DefinitionRef d) return false;
        return d.Definition.Interfaces.Any(i => Implements(i.Substitute(d.Arguments, []), target));
    }
}
