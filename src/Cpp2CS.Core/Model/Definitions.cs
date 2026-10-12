using System.Collections.Immutable;

namespace Cpp2CS.Model;

public enum TypeCategory { Class, Struct, Interface, Enum, Delegate }
public enum GenericConstraintKind { Unspecified, ReferenceType, ValueType }
public sealed record GenericParameterDefinition(GenericParameterId Id, string Name,
    GenericConstraintKind Kind, Sequence<TypeRef> Constraints);
public sealed record TypeDefinition(DefinitionId Id, string Namespace, string Name, TypeCategory Category,
    TypeRef? BaseType, Sequence<GenericParameterDefinition> Parameters, Evidence Evidence);
public sealed record FieldDefinition(DefinitionId Id, DefinitionId DeclaringType, string Name,
    TypeRef Type, bool IsStatic, Evidence Evidence);
public sealed record ParameterDefinition(string Name, TypeRef Type);
public sealed record ManagedSignature(bool HasThis, TypeRef ReturnType, Sequence<ParameterDefinition> Parameters);
public sealed record MethodDefinition(DefinitionId Id, DefinitionId DeclaringType, string Name,
    ManagedSignature Signature, Sequence<GenericParameterDefinition> Parameters, Evidence Evidence);

// 托管签名及其实例化结果与共享机器代码的 ABI 分开表示。
public sealed class DefinitionCatalog
{
    public ImmutableDictionary<DefinitionId, TypeDefinition> Types { get; }
    public ImmutableDictionary<DefinitionId, FieldDefinition> Fields { get; }
    public ImmutableDictionary<DefinitionId, MethodDefinition> Methods { get; }
    public DefinitionCatalog(IEnumerable<TypeDefinition> types, IEnumerable<FieldDefinition> fields, IEnumerable<MethodDefinition> methods)
    {
        Types = types.ToImmutableDictionary(x => x.Id);
        Fields = fields.ToImmutableDictionary(x => x.Id);
        Methods = methods.ToImmutableDictionary(x => x.Id);
        foreach (var type in Types.Values) ValidateParameters(type.Id, GenericOwner.Type, type.Parameters);
        foreach (var method in Methods.Values)
        {
            if (!Types.ContainsKey(method.DeclaringType)) throw new ArgumentException("方法所属类型缺失");
            ValidateParameters(method.Id, GenericOwner.Method, method.Parameters);
        }
        if (Fields.Values.Any(f => !Types.ContainsKey(f.DeclaringType))) throw new ArgumentException("字段所属类型缺失");
    }
    public ManagedSignature Instantiate(MethodInstance instance)
    {
        var method = Methods[instance.Definition];
        var type = Types[method.DeclaringType];
        if (type.Parameters.Count != instance.TypeArguments.Count || method.Parameters.Count != instance.MethodArguments.Count)
            throw new ArgumentException("泛型实参数量不匹配");
        var context = new GenericContext(type.Parameters.Select((p, i) => KeyValuePair.Create(p.Id, instance.TypeArguments[i]))
            .Concat(method.Parameters.Select((p, i) => KeyValuePair.Create(p.Id, instance.MethodArguments[i]))));
        return method.Signature with
        {
            ReturnType = context.Substitute(method.Signature.ReturnType),
            Parameters = new(method.Signature.Parameters.Select(p => p with { Type = context.Substitute(p.Type) }))
        };
    }
    private static void ValidateParameters(DefinitionId owner, GenericOwner kind, Sequence<GenericParameterDefinition> parameters)
    {
        for (var i = 0; i < parameters.Count; i++)
            if (parameters[i].Id != new GenericParameterId(owner, kind, i)) throw new ArgumentException("泛型参数归属或序号无效");
    }
}
