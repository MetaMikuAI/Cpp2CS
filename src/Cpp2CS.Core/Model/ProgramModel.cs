using System.Reflection;
using Cpp2CS.Images;

namespace Cpp2CS.Model;

/// <summary>托管类型引用。泛型实例的 Arguments 按 CLR 规则包含外层类型的实参。</summary>
public abstract record TypeRef;

/// <summary>没有类型定义可对应的类型（目前只有函数指针，按 nint 处理）。</summary>
public sealed record PrimitiveRef(string Name) : TypeRef
{
    public override string ToString() => Name;
}

public sealed record DefinitionRef(TypeDef Definition, IReadOnlyList<TypeRef> Arguments) : TypeRef
{
    public bool Equals(DefinitionRef? other) => other is not null && Definition == other.Definition && Arguments.SequenceEqual(other.Arguments);
    public override int GetHashCode() => Arguments.Aggregate(Definition.Index, (h, a) => HashCode.Combine(h, a));
    public override string ToString() => Arguments.Count == 0 ? Definition.Keyword ?? Definition.FullName : $"{Definition.FullName}<{string.Join(", ", Arguments)}>";
}

public sealed record ArrayRef(TypeRef Element, int Rank) : TypeRef
{
    /// <summary>SZARRAY 与 rank=1 的 ARRAY 是不同的 CLR 类型。</summary>
    public bool IsVector { get; init; } = Rank == 1;
    public override string ToString() => $"{Element}[{(Rank == 1 && !IsVector ? "*" : new string(',', Rank - 1))}]";
}

public sealed record PointerRef(TypeRef Element) : TypeRef
{
    public override string ToString() => $"{Element}*";
}

public sealed record ByRefRef(TypeRef Element) : TypeRef
{
    public override string ToString() => $"ref {Element}";
}

public sealed record GenericParameterRef(string Name, bool IsMethod, int Position) : TypeRef
{
    public GenericParameterDef? Parameter { get; init; }
    /// <summary>当前原生入口已证明使用引用共享 ABI；不改变元数据中的泛型约束。</summary>
    public bool SharedReference { get; init; }
    /// <summary>原生实例的标量布局见证；托管输出仍保留类型参数，仅允许复制、默认值和拆箱。</summary>
    public TypeRef? NativeScalar { get; init; }
    public DefinitionRef? ReferenceBase => Parameter?.Constraints.OfType<DefinitionRef>().FirstOrDefault(t => !t.Definition.IsValueType
        && !t.Definition.IsInterface && t.Definition.FullName is not ("System.Object" or "System.ValueType" or "System.Enum"));
    public bool IsReferenceConstrained => (Parameter?.Attributes & GenericParameterAttributes.ReferenceTypeConstraint) != 0 && Parameter is not null
        || ReferenceBase is not null;
    public bool IsReference => SharedReference || IsReferenceConstrained;
    // 约束是参数的语义信息，不改变其名称和槽位身份。
    public bool Equals(GenericParameterRef? other) => other is not null && Name == other.Name && IsMethod == other.IsMethod && Position == other.Position;
    public override int GetHashCode() => HashCode.Combine(Name, IsMethod, Position);
    public override string ToString() => Name;
}

public static class TypeRefs
{
    /// <summary>以类与方法实参代入泛型参数；实参不足的参数保持原样。</summary>
    public static TypeRef Substitute(this TypeRef type, IReadOnlyList<TypeRef> typeArguments, IReadOnlyList<TypeRef> methodArguments) => type switch
    {
        GenericParameterRef { IsMethod: false } g when g.Position < typeArguments.Count => typeArguments[g.Position],
        GenericParameterRef { IsMethod: true } g when g.Position < methodArguments.Count => methodArguments[g.Position],
        DefinitionRef { Arguments.Count: > 0 } d => d with { Arguments = d.Arguments.Select(a => a.Substitute(typeArguments, methodArguments)).ToArray() },
        ArrayRef a => a with { Element = a.Element.Substitute(typeArguments, methodArguments) },
        PointerRef p => p with { Element = p.Element.Substitute(typeArguments, methodArguments) },
        ByRefRef r => r with { Element = r.Element.Substitute(typeArguments, methodArguments) },
        _ => type,
    };
}

/// <summary>泛型参数：名称、位置、约束标志（class/struct/new()/协变逆变）与类型约束。</summary>
public sealed class GenericParameterDef
{
    public required string Name { get; init; }
    public required int Position { get; init; }
    public required GenericParameterAttributes Attributes { get; init; }
    public IReadOnlyList<TypeRef> Constraints { get; internal set; } = [];
    public override string ToString() => Name;
}

/// <summary>自定义特性的参数值。Type 为编码时的类型（基元、string、System.Type、枚举、数组）；
/// Value 为基元值、string、TypeRef（typeof）、AttributeValue[]（数组）或 null。</summary>
public sealed record AttributeValue(TypeRef Type, object? Value);

public sealed record CustomAttributeDef(
    MethodDef Constructor,
    IReadOnlyList<AttributeValue> Arguments,
    IReadOnlyList<(FieldDef Field, AttributeValue Value)> Fields,
    IReadOnlyList<(PropertyDef Property, AttributeValue Value)> Properties);

public sealed class AssemblyDef
{
    /// <summary>映像名（含扩展名，如 Assembly-CSharp.dll）。</summary>
    public required string Name { get; init; }
    /// <summary>程序集名（不含扩展名）。</summary>
    public required string AssemblyName { get; init; }
    public required Version Version { get; init; }
    public required string Culture { get; init; }
    /// <summary>公钥令牌，8 字节；无强名称时为空。</summary>
    /// <summary>完整公钥，空表示无强名称。</summary>
    public required byte[] PublicKey { get; init; }
    public IReadOnlyList<CustomAttributeDef> CustomAttributes { get; internal set; } = [];
    public IReadOnlyList<TypeDef> Types { get; internal set; } = [];
    public override string ToString() => Name;
}

public sealed class TypeDef
{
    public required int Index { get; init; }
    public required string Assembly { get; init; }
    public required string Namespace { get; init; }
    /// <summary>元数据名，泛型类型带 `N 后缀。</summary>
    public required string Name { get; init; }
    public required uint Token { get; init; }
    public required TypeAttributes Attributes { get; init; }
    public required bool IsValueType { get; init; }
    public required bool IsEnum { get; init; }
    public TypeDef? DeclaringType { get; internal set; }
    /// <summary>本类型声明的泛型参数（嵌套类型按 CLR 规则包含外层类型的参数）。</summary>
    public IReadOnlyList<GenericParameterDef> GenericParameters { get; internal set; } = [];
    public TypeRef? BaseType { get; internal set; }
    public IReadOnlyList<TypeRef> Interfaces { get; internal set; } = [];
    public IReadOnlyList<FieldDef> Fields { get; internal set; } = [];
    public IReadOnlyList<MethodDef> Methods { get; internal set; } = [];
    public IReadOnlyList<PropertyDef> Properties { get; internal set; } = [];
    public IReadOnlyList<EventDef> Events { get; internal set; } = [];
    public IReadOnlyList<TypeDef> NestedTypes { get; internal set; } = [];
    public IReadOnlyList<CustomAttributeDef> CustomAttributes { get; internal set; } = [];
    /// <summary>值类型为实例数据大小（不含对象头），引用类型为含对象头的实例大小；未知为 -1。</summary>
    public int Size { get; internal set; } = -1;
    /// <summary>元数据中的字段打包上限；0 为默认，-1 为未知。</summary>
    public int PackingSize { get; init; } = -1;
    /// <summary>元数据是否使用默认类大小；null 表示尚未读取。</summary>
    public bool? ClassSizeIsDefault { get; init; }
    /// <summary>vtable 槽位到方法；接口方法槽位由运行时按 interface offset 拼接，元数据中为 MethodRef/MethodDef。</summary>
    public IReadOnlyList<MethodRef?> VTable { get; internal set; } = [];
    /// <summary>(接口, 起始槽位)。</summary>
    public IReadOnlyList<(TypeRef Interface, int Offset)> InterfaceOffsets { get; internal set; } = [];

    public bool IsInterface => (Attributes & TypeAttributes.Interface) != 0;
    /// <summary>C# 内建类型关键字（int、string……），其余为 null。</summary>
    public string? Keyword => Namespace != "System" || DeclaringType is not null ? null : Name switch
    {
        "Void" => "void", "Boolean" => "bool", "Char" => "char", "SByte" => "sbyte", "Byte" => "byte",
        "Int16" => "short", "UInt16" => "ushort", "Int32" => "int", "UInt32" => "uint", "Int64" => "long", "UInt64" => "ulong",
        "Single" => "float", "Double" => "double", "Decimal" => "decimal", "String" => "string", "Object" => "object",
        "IntPtr" => "nint", "UIntPtr" => "nuint",
        _ => null,
    };
    public string SimpleName => Name.IndexOf('`') is var tick and >= 0 ? Name[..tick] : Name;
    public string FullName => DeclaringType is not null ? $"{DeclaringType.FullName}.{SimpleName}" : Namespace.Length == 0 ? SimpleName : $"{Namespace}.{SimpleName}";
    public override string ToString() => FullName;
}

public sealed class FieldDef
{
    public required int Index { get; init; }
    public required TypeDef Owner { get; init; }
    public required string Name { get; init; }
    public required TypeRef Type { get; init; }
    public required FieldAttributes Attributes { get; init; }
    /// <summary>实例字段相对对象起始（引用类型含对象头，值类型已减去对象头）；静态字段相对 static_fields；-1 未知。</summary>
    public required int Offset { get; init; }
    public object? Constant { get; init; }
    /// <summary>HasFieldRVA 字段的初始数据（数组初始化器的源数据），长度为字段类型的大小；其他字段为 null。</summary>
    public byte[]? InitialValue { get; internal set; }
    public uint Token { get; init; }
    public IReadOnlyList<CustomAttributeDef> CustomAttributes { get; internal set; } = [];
    public bool IsStatic => (Attributes & FieldAttributes.Static) != 0;
    public bool IsThreadStatic { get; internal set; }
    public override string ToString() => $"{Owner.FullName}.{Name}";
}

public sealed record ParameterDef(string Name, TypeRef Type, ParameterAttributes Attributes, object? DefaultValue, bool HasDefault)
{
    public uint Token { get; init; }
    public IReadOnlyList<CustomAttributeDef> CustomAttributes { get; internal set; } = [];
}

/// <summary>已知 C ABI 导入的库名和精确入口；签名由所属方法描述。</summary>
public sealed record NativeImport(string Library, string EntryPoint)
{
    public System.Runtime.InteropServices.CallingConvention CallingConvention { get; init; } = System.Runtime.InteropServices.CallingConvention.Cdecl;
    public System.Runtime.InteropServices.CharSet CharSet { get; init; } = System.Runtime.InteropServices.CharSet.None;
    public bool ExactSpelling { get; init; } = true;
}

public sealed class MethodDef
{
    public required int Index { get; init; }
    public required TypeDef Owner { get; init; }
    public required string Name { get; init; }
    public required uint Token { get; init; }
    public required MethodAttributes Attributes { get; init; }
    public required MethodImplAttributes ImplAttributes { get; init; }
    public required int Slot { get; init; }
    public NativeImport? NativeImport { get; init; }
    public TypeRef ReturnType { get; internal set; } = new PrimitiveRef("void");
    public IReadOnlyList<ParameterDef> Parameters { get; internal set; } = [];
    public IReadOnlyList<GenericParameterDef> GenericParameters { get; internal set; } = [];
    public IReadOnlyList<CustomAttributeDef> CustomAttributes { get; internal set; } = [];
    /// <summary>返回值参数行（序号 0）的令牌：v31 起 Il2CppMethodDefinition.returnParameterToken；更早版本没有，为 0。</summary>
    public uint ReturnParameterToken { get; init; }
    /// <summary>返回值上的特性（挂在返回值参数令牌上；v31 之前元数据不保存，为空）。</summary>
    public IReadOnlyList<CustomAttributeDef> ReturnAttributes { get; internal set; } = [];
    /// <summary>非共享实现的代码地址（首选基址下的 VA）；0 表示无实现（抽象、extern 或仅有泛型实例）。</summary>
    public ulong Address { get; internal set; }

    public bool IsStatic => (Attributes & MethodAttributes.Static) != 0;
    public bool IsVirtual => (Attributes & MethodAttributes.Virtual) != 0;
    public bool IsAbstract => (Attributes & MethodAttributes.Abstract) != 0;
    public override string ToString() => $"{Owner.FullName}.{Name}";
}

public sealed class PropertyDef
{
    public required string Name { get; init; }
    public required PropertyAttributes Attributes { get; init; }
    public required uint Token { get; init; }
    public MethodDef? Getter { get; init; }
    public MethodDef? Setter { get; init; }
    public IReadOnlyList<CustomAttributeDef> CustomAttributes { get; internal set; } = [];
    public override string ToString() => Name;
}

public sealed class EventDef
{
    public required string Name { get; init; }
    public required TypeRef Type { get; init; }
    public required EventAttributes Attributes { get; init; }
    public required uint Token { get; init; }
    public MethodDef? Add { get; init; }
    public MethodDef? Remove { get; init; }
    public MethodDef? Raise { get; init; }
    public IReadOnlyList<CustomAttributeDef> CustomAttributes { get; internal set; } = [];
    public override string ToString() => Name;
}

/// <summary>方法引用：泛型定义上的方法加上类与方法实参（可能为空）。</summary>
public sealed record MethodRef(MethodDef Method, IReadOnlyList<TypeRef> TypeArguments, IReadOnlyList<TypeRef> MethodArguments)
{
    public static MethodRef Open(MethodDef method) => new(method,
        method.Owner.GenericParameters.Select(p => (TypeRef)new GenericParameterRef(p.Name, false, p.Position) { Parameter = p }).ToArray(),
        method.GenericParameters.Select(p => (TypeRef)new GenericParameterRef(p.Name, true, p.Position) { Parameter = p }).ToArray());

    public bool Equals(MethodRef? other) => other is not null && Method == other.Method && TypeArguments.SequenceEqual(other.TypeArguments) && MethodArguments.SequenceEqual(other.MethodArguments);
    public override int GetHashCode() => MethodArguments.Aggregate(TypeArguments.Aggregate(Method.Index, (h, a) => HashCode.Combine(h, a)), (h, a) => HashCode.Combine(h, a));
    public TypeRef DeclaringType => new DefinitionRef(Method.Owner, TypeArguments);
    public override string ToString() => MethodArguments.Count == 0 ? $"{DeclaringType}.{Method.Name}" : $"{DeclaringType}.{Method.Name}<{string.Join(", ", MethodArguments)}>";
}

public sealed record FieldRef(FieldDef Field, TypeRef DeclaringType)
{
    public override string ToString() => $"{DeclaringType}.{Field.Name}";
}

public enum UsageKind { TypeInfo = 1, Il2CppType = 2, MethodDef = 3, FieldInfo = 4, StringLiteral = 5, MethodRef = 6 }

/// <summary>运行时元数据槽位的已解码内容。Value 为 TypeRef / MethodRef / FieldRef / string。</summary>
public sealed record Usage(UsageKind Kind, uint Index, object Value)
{
    public override string ToString() => Kind == UsageKind.StringLiteral ? $"\"{Value}\"" : $"{Kind}({Value})";
}

/// <summary>一段代码的托管所有者：非共享方法或泛型实例（共享实现可对应多个实例）。</summary>
public sealed record CodeOwner(MethodRef Method, bool IsInstance);

public sealed class ProgramModel
{
    public required ImageDocument Image { get; init; }
    public required double MetadataVersion { get; init; }
    public required IReadOnlyList<AssemblyDef> Assemblies { get; init; }
    public required IReadOnlyList<TypeDef> Types { get; init; }
    public required IReadOnlyList<MethodDef> Methods { get; init; }
    public required IReadOnlyList<FieldDef> Fields { get; init; }
    /// <summary>运行时 Il2CppType 表（metadata registration types）对应的引用。</summary>
    public required IReadOnlyList<TypeRef> RuntimeTypes { get; init; }
    public required IReadOnlyList<MethodRef> MethodSpecs { get; init; }
    public required IReadOnlyList<FieldRef> FieldRefs { get; init; }
    public required IReadOnlyList<string> StringLiterals { get; init; }
    /// <summary>代码地址到托管所有者。</summary>
    public required IReadOnlyDictionary<ulong, IReadOnlyList<CodeOwner>> Code { get; init; }
    private readonly Dictionary<ulong, Usage?> slots = new();

    /// <summary>
    /// 读取元数据槽位（v27+：全局变量初值为编码令牌 ((kind&lt;&lt;29)|(index&lt;&lt;1))+1）。
    /// 编码不合法或索引越界返回 null。
    /// </summary>
    public Usage? UsageAt(ulong slot)
    {
        if (slots.TryGetValue(slot, out var cached)) return cached;
        Usage? usage = null;
        var mapping = Image.Resolve(slot);
        if (mapping.Kind == AddressKind.FileBacked && mapping.AvailableBytes >= 8 && !mapping.Range!.Executable)
        {
            var value = Image.ReadPointer(slot);
            if (value is { } raw && raw < uint.MaxValue)
            {
                var token = (uint)raw;
                var kind = token >> 29;
                var index = (token & 0x1FFFFFFF) >> 1;
                if (kind is >= 1 and <= 6 && raw == ((kind << 29) | (index << 1)) + 1) usage = DecodeToken(kind, index);
            }
        }
        slots[slot] = usage;
        return usage;
    }

    public Usage? DecodeToken(uint kind, uint index) => (UsageKind)kind switch
    {
        UsageKind.TypeInfo or UsageKind.Il2CppType when index < RuntimeTypes.Count => new((UsageKind)kind, index, RuntimeTypes[(int)index]),
        UsageKind.MethodDef when index < Methods.Count => new(UsageKind.MethodDef, index, new MethodRef(Methods[(int)index], [], [])),
        UsageKind.FieldInfo when index < FieldRefs.Count => new(UsageKind.FieldInfo, index, FieldRefs[(int)index]),
        UsageKind.StringLiteral when index < StringLiterals.Count => new(UsageKind.StringLiteral, index, StringLiterals[(int)index]),
        UsageKind.MethodRef when index < MethodSpecs.Count => new(UsageKind.MethodRef, index, MethodSpecs[(int)index]),
        _ => null,
    };
}
