using System.Reflection;

namespace Cpp2CS.Model;

public abstract record TypeReference;
public sealed record NamedType(int Definition, IReadOnlyList<TypeReference> Arguments) : TypeReference;
public sealed record VariableType(int Parameter, bool Method, int Owner, int Position) : TypeReference;
public sealed record PointerType(TypeReference Element) : TypeReference;
public sealed record ReferenceType(TypeReference Element) : TypeReference;
/// <summary>向量和一维多维数组有不同的元数据编码。</summary>
public sealed record ArrayType(TypeReference Element, int Rank, bool Vector) : TypeReference;

public sealed record GenericParameter(string Name, int Position, GenericParameterAttributes Flags,
    IReadOnlyList<TypeReference> Constraints);
public sealed record AssemblyDefinition(string Name, string Culture, int Major, int Minor, int Build, int Revision, int Image);
public sealed record ImageDefinition(string Name, int Assembly, int FirstType, int TypeCount);
public sealed record TypeDefinition(string Namespace, string Name, int? DeclaringType, TypeReference? Parent,
    TypeAttributes Flags, bool ValueType, IReadOnlyList<TypeReference> Interfaces, IReadOnlyList<GenericParameter> GenericParameters,
    int FirstField, int FieldCount, int FirstMethod, int MethodCount, uint Token);

public enum FieldStorage { Instance, Static, ThreadStatic, Literal }
/// <summary>偏移相对实例数据、静态区或线程静态区。开放泛型没有实例布局。</summary>
public sealed record FieldDefinition(int Owner, int Ordinal, string Name, TypeReference Type, FieldAttributes Flags,
    FieldStorage Storage, int? Offset, uint Token);
public sealed record ParameterDefinition(string Name, TypeReference Type, ParameterAttributes Flags);
public sealed record MethodDefinition(int Owner, string Name, uint Token, MethodAttributes Flags, MethodImplAttributes ImplFlags,
    TypeReference ReturnType, IReadOnlyList<ParameterDefinition> Parameters, IReadOnlyList<GenericParameter> GenericParameters);
public sealed record MethodInstance(int Definition, IReadOnlyList<TypeReference> TypeArguments, IReadOnlyList<TypeReference> MethodArguments);
public sealed record MetadataModel(IReadOnlyList<AssemblyDefinition> Assemblies, IReadOnlyList<ImageDefinition> Images,
    IReadOnlyList<TypeDefinition> Types, IReadOnlyList<FieldDefinition> Fields, IReadOnlyList<MethodDefinition> Methods,
    IReadOnlyList<TypeReference> RuntimeTypes, IReadOnlyList<NamedType?> GenericClasses,
    IReadOnlyList<MethodInstance> MethodInstances, IReadOnlyList<string> StringLiterals);

/// <summary>入口使用 RVA。相同入口可以对应多个定义或规格，下标保留各自的身份。</summary>
public readonly record struct MethodCode(ulong? Entry, int? Invoker);
public sealed record CodeMap(ulong CodeRegistration, ulong MetadataRegistration, IReadOnlyList<MethodCode> Methods,
    IReadOnlyList<MethodCode> MethodInstances, IReadOnlyList<ulong?> Invokers);
