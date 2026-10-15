using System.Text.Json;

namespace Cpp2CS.Metadata;

public sealed record CaseSpec(string BinarySha256, string Assembly, string[] Types);
public sealed record Field(string Name, string Type, int Offset, bool ReadOnly, bool Public);
public sealed record Parameter(string Name, string Type, string? Default);
public sealed record Method(string Name, string Token, string Address, string ReturnType, bool Static,
    string? Property, Parameter[] Parameters, string NativePrototype);
public sealed record TypeModel(string Name, string NativeName, bool ValueType, bool Sealed,
    Field[] Fields, Method[] Methods);
public sealed record EnumModel(string Name, Dictionary<string, long> Members);
public sealed record Catalog(string BinarySha256, string Assembly, string ObjectConstructorAddress, TypeModel[] Types, EnumModel[] Enums)
{
    public TypeModel Type(string name) => Types.Single(t => t.Name == name);
    public bool IsEnum(string name) => Enums.Any(t => t.Name == name);
    public static readonly JsonSerializerOptions Json = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase, PropertyNameCaseInsensitive = true, WriteIndented = true
    };
}
