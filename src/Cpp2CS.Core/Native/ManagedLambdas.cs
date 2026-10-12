using System.Reflection;

namespace Cpp2CS.Native;

public sealed partial class ManagedNames
{
    public (string Name, string Type, bool Public)? StaticField(string typeName, string nativeName)
    {
        var (name, arguments) = SplitGeneric(typeName); var owner = FindDefinition(name);
        var handle = owner?.DefinitionWithArity(name, arguments.Length) ?? default;
        if (owner is null || handle.IsNil) return null;
        var fields = owner.reader.GetTypeDefinition(handle).GetFields().Select(owner.reader.GetFieldDefinition).Where(f =>
            (f.Attributes & FieldAttributes.Static) != 0 && owner.reader.GetString(f.Name) == nativeName).ToArray();
        return fields.Length == 1 ? (nativeName, fields[0].DecodeSignature(owner, new GenericNames(arguments, [])),
            (fields[0].Attributes & FieldAttributes.FieldAccessMask) == FieldAttributes.Public) : null;
    }
    public string[] StaticGetters(string typeName, string returnType)
    {
        var (name, arguments) = SplitGeneric(typeName); var owner = FindDefinition(name);
        var handle = owner?.DefinitionWithArity(name, arguments.Length) ?? default;
        if (owner is null || handle.IsNil) return [];
        return owner.reader.GetTypeDefinition(handle).GetProperties().Select(owner.reader.GetPropertyDefinition).Select(p => p.GetAccessors().Getter)
            .Where(h => !h.IsNil).Select(owner.reader.GetMethodDefinition).Where(m =>
                (m.Attributes & MethodAttributes.Static) != 0 && (m.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public &&
                m.DecodeSignature(owner, new GenericNames(arguments, [])) is { ParameterTypes.Length: 0 } s && s.ReturnType == returnType)
            .Select(m => owner.reader.GetString(m.Name)).ToArray();
    }
    public string? GeneratedLambdaOrigin(NativeMethod method)
    {
        var parts = method.Name.Split("$$");
        if (parts.Length != 2 || !parts[1].StartsWith('<') || parts[1].IndexOf(">b__", StringComparison.Ordinal) is not > 1 || !types.TryGetValue(parts[0], out var handle)) return null;
        var definition = reader.GetTypeDefinition(handle);
        var candidates = definition.GetMethods().Select(reader.GetMethodDefinition).Where(m => reader.GetString(m.Name) == parts[1]).ToArray();
        if (candidates.Length != 1 || !candidates[0].GetCustomAttributes().Select(AttributeName).Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute") &&
            !definition.GetCustomAttributes().Select(AttributeName).Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute")) return null;
        return parts[1][1..parts[1].IndexOf(">b__", StringComparison.Ordinal)];
    }
    public bool IsClosureType(string name, NativeMethod enclosing)
    {
        if (!types.TryGetValue(name, out var handle)) return false;
        var type = reader.GetTypeDefinition(handle);
        return type.IsNested && GetTypeFromDefinition(reader, type.GetDeclaringType(), 0) == enclosing.Name.Split("$$")[0] &&
            type.GetCustomAttributes().Select(AttributeName).Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute") &&
            BaseTypeOf(name) == "System.Object" && type.GetFields().Select(reader.GetFieldDefinition).Any(f => (f.Attributes & FieldAttributes.Static) == 0);
    }
    public bool IsCapturingLambda(NativeMethod enclosing, NativeMethod lambda, string environment, string delegateType)
    {
        if (!IsClosureType(environment, enclosing) || lambda.Name.Split("$$")[0] != environment || GeneratedLambdaOrigin(lambda) is not { } origin ||
            origin != (GeneratedLambdaOrigin(enclosing) ?? enclosing.Name.Split("$$")[1]) || BaseTypeOf(delegateType) != "System.MulticastDelegate") return false;
        var invoke = SignatureOf(delegateType, "Invoke"); var target = SignatureOf(environment, lambda.Name.Split("$$")[1]);
        string Canonical(string type)
        {
            type = type switch { "bool" => "System.Boolean", "int" => "System.Int32", "long" => "System.Int64", "float" => "System.Single", "double" => "System.Double", "string" => "System.String", "object" => "System.Object", _ => type };
            var found = types.Keys.Where(t => t == type || t.EndsWith("." + type, StringComparison.Ordinal)).ToArray();
            return found.Length == 1 ? found[0] : type;
        }
        return invoke is { } a && target is { } b && Canonical(a.ReturnType) == Canonical(b.ReturnType) && a.ParameterTypes.Select(Canonical).SequenceEqual(b.ParameterTypes.Select(Canonical));
    }
    public bool IsNonCapturingCachedLambda(NativeMethod enclosing, NativeMethod lambda, DelegateCacheStatement cache)
    {
        var ownerName = lambda.Name.Split("$$")[0]; var methodName = lambda.Name.Split("$$")[1];
        if (!types.TryGetValue(ownerName, out var handle)) return false;
        var type = reader.GetTypeDefinition(handle);
        if (!type.IsNested || GetTypeFromDefinition(reader, type.GetDeclaringType(), 0) != enclosing.Name.Split("$$")[0] ||
            !type.GetCustomAttributes().Select(AttributeName).Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute") ||
            type.GetFields().Select(reader.GetFieldDefinition).Any(f => (f.Attributes & FieldAttributes.Static) == 0)) return false;
        var prefix = "<" + enclosing.Name.Split("$$")[1] + ">b__";
        if (!methodName.StartsWith(prefix)) return false;
        var field = SourceMember(ownerName, cache.Cache.Field.Name);
        if (field is null || field.Value.Name != "<>9__" + methodName[prefix.Length..] ||
            cache.Target is not MemberExpression singleton || SourceMember(ownerName, singleton.Field.Name)?.Name != "<>9" ||
            SourceMember(ownerName, singleton.Field.Name)?.Type != ownerName ||
            cache.Cache.Receiver is not MemberExpression { Receiver: MetadataExpression info } || info.Reference.Name != ownerName + "_TypeInfo") return false;
        var invoke = SignatureOf(field.Value.Type, "Invoke");
        var target = SignatureOf(ownerName, methodName);
        return invoke is { } a && target is { } b && a.ReturnType == b.ReturnType && a.ParameterTypes.SequenceEqual(b.ParameterTypes);
    }
}
