using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;

namespace Cpp2CS.Native;

public sealed record GenericNames(string[] Types, string[] Methods);
public sealed partial class ManagedNames : ISignatureTypeProvider<string, GenericNames>, IDisposable
{
    private readonly PEReader pe;
    private readonly Stream stream;
    private readonly MetadataReader reader;
    private readonly string directory;
    private readonly Dictionary<string, ManagedNames> dependencies = [];
    private readonly Dictionary<string, TypeDefinitionHandle> types = [];
    public Dictionary<(string Type, string Field), string> FieldTypes { get; } = [];
    public Dictionary<(string Type, long Value), string> EnumNames { get; } = [];
    public ManagedNames(string path)
    {
        directory = Path.GetDirectoryName(path)!;
        stream = File.OpenRead(path); pe = new PEReader(stream); reader = pe.GetMetadataReader();
        foreach (var handle in reader.TypeDefinitions)
        {
            var name = GetTypeFromDefinition(reader, handle, 0);
            types.TryAdd(name, handle);
            var type = reader.GetTypeDefinition(handle);
            var isEnum = type.BaseType.Kind == HandleKind.TypeReference && GetTypeFromReference(reader, (TypeReferenceHandle)type.BaseType, 0) == "System.Enum";
            foreach (var fieldHandle in type.GetFields())
            {
                var field = reader.GetFieldDefinition(fieldHandle);
                var fieldName = reader.GetString(field.Name);
                FieldTypes[(name, fieldName)] = field.DecodeSignature(this, new GenericNames([], []));
                if (!isEnum || field.GetDefaultValue().IsNil) continue;
                var constant = reader.GetConstant(field.GetDefaultValue());
                var blob = reader.GetBlobReader(constant.Value);
                long? value = constant.TypeCode switch { ConstantTypeCode.Int32 => blob.ReadInt32(), ConstantTypeCode.UInt32 => blob.ReadUInt32(), ConstantTypeCode.Int64 => blob.ReadInt64(), ConstantTypeCode.Int16 => blob.ReadInt16(), ConstantTypeCode.Byte => blob.ReadByte(), _ => null };
                if (value is not null) EnumNames.TryAdd((name, value.Value), fieldName);
            }
        }
    }
    public string? ReturnOf(string methodReference)
    {
        var text = methodReference.StartsWith("Method$") ? methodReference[7..] : methodReference;
        var paren = text.IndexOf('(');
        if (paren >= 0) text = text[..paren];
        var separator = LastTopLevelDot(text);
        if (separator < 0) return null;
        var (typeName, typeArguments) = SplitGeneric(text[..separator]);
        var (methodName, methodArguments) = SplitGeneric(text[(separator + 1)..]);
        var owner = FindDefinition(typeName);
        var handle = owner?.DefinitionWithArity(typeName, typeArguments.Length) ?? default;
        if (owner is null || handle.IsNil) return null;
        var found = owner.reader.GetTypeDefinition(handle).GetMethods().Select(owner.reader.GetMethodDefinition)
            .Where(m => owner.reader.GetString(m.Name) == methodName && m.GetGenericParameters().Count == methodArguments.Length).ToArray();
        var returns = found.Select(m => m.DecodeSignature(owner, new GenericNames(typeArguments, methodArguments)).ReturnType).Distinct().ToArray();
        return returns.Length == 1 ? returns[0] : null;
    }
    public MethodSignature<string>? SignatureOf(string typeName, string methodName)
    {
        var (name, arguments) = SplitGeneric(typeName);
        var (methodRoot, methodArguments) = SplitGeneric(methodName);
        var owner = FindDefinition(name);
        if (owner is null) return null;
        var handle = owner.DefinitionWithArity(name, arguments.Length);
        if (handle.IsNil) return null;
        var methods = owner.reader.GetTypeDefinition(handle).GetMethods().Select(owner.reader.GetMethodDefinition).Where(m => owner.reader.GetString(m.Name) == methodRoot &&
            (methodArguments.Length == 0 || m.GetGenericParameters().Count == methodArguments.Length)).ToArray();
        return methods.Length == 1 ? methods[0].DecodeSignature(owner, new GenericNames(arguments, methodArguments)) : null;
    }
    public string? BaseTypeOf(string typeName)
    {
        var (name, args) = SplitGeneric(typeName);
        if (!types.TryGetValue(name, out var handle)) return FindDefinition(name)?.BaseTypeOf(typeName);
        var baseType = reader.GetTypeDefinition(handle).BaseType;
        if (baseType.IsNil) return null;
        return baseType.Kind switch
        {
            HandleKind.TypeDefinition => GetTypeFromDefinition(reader, (TypeDefinitionHandle)baseType, 0),
            HandleKind.TypeReference => GetTypeFromReference(reader, (TypeReferenceHandle)baseType, 0),
            HandleKind.TypeSpecification => GetTypeFromSpecification(reader, new GenericNames(args, []), (TypeSpecificationHandle)baseType, 0),
            _ => null
        };
    }
    public string? FieldTypeOf(string typeName, string fieldName)
    {
        var (name, arguments) = SplitGeneric(typeName);
        var owner = FindDefinition(name);
        var handle = owner?.DefinitionWithArity(name, arguments.Length) ?? default;
        if (owner is null || handle.IsNil) return null;
        var fields = owner.reader.GetTypeDefinition(handle).GetFields().Select(owner.reader.GetFieldDefinition)
            .Where(f => owner.reader.GetString(f.Name) == fieldName).ToArray();
        return fields.Length == 1 ? fields[0].DecodeSignature(owner, new GenericNames(arguments, [])) : null;
    }
    public bool IsVoidSingleArgumentDelegate(string name)
    {
        var (root, _) = SplitGeneric(name);
        if (!types.TryGetValue(root, out var handle)) return false;
        var type = reader.GetTypeDefinition(handle);
        if (type.BaseType.Kind != HandleKind.TypeReference || GetTypeFromReference(reader, (TypeReferenceHandle)type.BaseType, 0) != "System.MulticastDelegate") return false;
        var signature = SignatureOf(name, "Invoke");
        return signature is { ReturnType: "System.Void", ParameterTypes.Length: 1 } s && IsReferenceType(s.ParameterTypes[0]);
    }
    private bool IsReferenceType(string type)
    {
        if (type is "System.Object" or "System.String" || type.EndsWith("[]")) return true;
        var (root, _) = SplitGeneric(type);
        if (!types.ContainsKey(root)) return false;
        return BaseTypeOf(type) is { } parent && parent is not ("System.ValueType" or "System.Enum");
    }
    public bool IsPropertyGetter(string typeName, string methodName)
    {
        var (name, _) = SplitGeneric(typeName);
        if (!types.TryGetValue(name, out var handle)) return false;
        return reader.GetTypeDefinition(handle).GetProperties().Select(reader.GetPropertyDefinition)
            .Select(p => p.GetAccessors().Getter).Any(g => !g.IsNil && reader.GetString(reader.GetMethodDefinition(g).Name) == methodName);
    }
    public object? CompilerContext(NativeMethod method, Symbols symbols, bool highLevelRecovered = false)
    {
        var owner = method.Name.Split("$$")[0];
        if (!types.TryGetValue(SplitGeneric(owner).Name, out var handle)) return null;
        var type = reader.GetTypeDefinition(handle);
        string EntityName(EntityHandle h) => h.Kind switch
        {
            HandleKind.TypeDefinition => GetTypeFromDefinition(reader, (TypeDefinitionHandle)h, 0),
            HandleKind.TypeReference => GetTypeFromReference(reader, (TypeReferenceHandle)h, 0),
            HandleKind.TypeSpecification => GetTypeFromSpecification(reader, new([], []), (TypeSpecificationHandle)h, 0),
            _ => ""
        };
        string AttributeName(CustomAttributeHandle h)
        {
            var constructor = reader.GetCustomAttribute(h).Constructor;
            return constructor.Kind == HandleKind.MemberReference ? EntityName(reader.GetMemberReference((MemberReferenceHandle)constructor).Parent) :
                constructor.Kind == HandleKind.MethodDefinition ? EntityName(reader.GetMethodDefinition((MethodDefinitionHandle)constructor).GetDeclaringType()) : "";
        }
        var interfaces = type.GetInterfaceImplementations().Select(h => EntityName(reader.GetInterfaceImplementation(h).Interface)).ToArray();
        var attributes = type.GetCustomAttributes().Select(AttributeName).ToArray();
        var methods = type.GetMethods().Select(h => (Handle: h, Definition: reader.GetMethodDefinition(h))).ToArray();
        var targetMethods = methods.Where(m => reader.GetString(m.Definition.Name) == method.Name.Split("$$")[1]).ToArray();
        bool MatchesAddress(MethodDefinition definition)
        {
            foreach (var attribute in definition.GetCustomAttributes())
            {
                if (AttributeName(attribute) != "Il2CppDummyDll.AddressAttribute") continue;
                var blob = reader.GetBlobReader(reader.GetCustomAttribute(attribute).Value);
                if (blob.ReadUInt16() != 1) return false;
                var count = blob.ReadUInt16();
                for (var i = 0; i < count; i++)
                {
                    var kind = blob.ReadByte(); var typeCode = blob.ReadByte();
                    if (kind is not (0x53 or 0x54) || typeCode != 0x0e) return false;
                    var key = blob.ReadSerializedString(); var value = blob.ReadSerializedString();
                    if (key is "RVA" or "VA" && value is not null && Convert.ToUInt64(value.StartsWith("0x") ? value[2..] : value, 16) == method.Address) return true;
                }
            }
            return false;
        }
        var exactMethods = targetMethods.Where(m => MatchesAddress(m.Definition)).ToArray();
        if (exactMethods.Length > 0) targetMethods = exactMethods;
        var linkedStates = new List<string>();
        foreach (var target in targetMethods)
            foreach (var attribute in target.Definition.GetCustomAttributes())
                if (AttributeName(attribute) is "System.Runtime.CompilerServices.AsyncStateMachineAttribute" or "System.Runtime.CompilerServices.IteratorStateMachineAttribute")
                {
                    var blob = reader.GetBlobReader(reader.GetCustomAttribute(attribute).Value);
                    if (blob.ReadUInt16() == 1 && blob.ReadSerializedString() is { } state) linkedStates.Add(state);
                }
        var generated = attributes.Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute") ||
            targetMethods.Any(m => m.Definition.GetCustomAttributes().Select(AttributeName).Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute"));
        var async = interfaces.Contains("System.Runtime.CompilerServices.IAsyncStateMachine");
        var iterator = interfaces.Contains("System.Collections.IEnumerator");
        if (!generated && !async && !iterator && linkedStates.Count == 0) return null;
        return new
        {
            kind = async ? "async-state-machine" : iterator ? "iterator-state-machine" : linkedStates.Count > 0 ? "state-machine-entry" : "compiler-generated-environment",
            type = owner,
            definitionToken = $"0x{System.Reflection.Metadata.Ecma335.MetadataTokens.GetToken(handle):x8}",
            interfaces, linkedStateTypes = linkedStates,
            targetDefinitionTokens = targetMethods.Select(m => $"0x{System.Reflection.Metadata.Ecma335.MetadataTokens.GetToken(m.Handle):x8}"),
            targetIdentityMatchedByAddressAttribute = exactMethods.Length > 0,
            fields = FieldTypes.Where(p => p.Key.Type == SplitGeneric(owner).Name).Select(p => new { name = p.Key.Field, type = p.Value }),
            methods = methods.Select(m => new
            {
                name = reader.GetString(m.Definition.Name),
                definitionToken = $"0x{System.Reflection.Metadata.Ecma335.MetadataTokens.GetToken(m.Handle):x8}",
                nativeCandidates = symbols.Methods.Values.SelectMany(v => v).Where(n => n.Name == owner + "$$" + reader.GetString(m.Definition.Name)).Select(n => $"0x{n.Address:x}").ToArray()
            }),
            source = "DummyDLL definitions, interfaces and attributes; native addresses are candidates, not identity",
            highLevelAwaitOrYieldRecovered = highLevelRecovered
        };
    }
    public static (string Name, string[] Arguments) SplitGeneric(string text)
    {
        var start = text.IndexOf('<');
        if (start <= 0 || !text.EndsWith('>') || text[start - 1] == '.') return (text, []);
        var args = new List<string>(); var depth = 0; var last = start + 1;
        for (var i = last; i < text.Length - 1; i++)
        {
            if (text[i] == '<') depth++;
            if (text[i] == '>') depth--;
            if (text[i] == ',' && depth == 0) { args.Add(text[last..i].Trim()); last = i + 1; }
        }
        args.Add(text[last..^1].Trim());
        return (text[..start], args.ToArray());
    }
    public static int LastTopLevelDot(string text)
    {
        var depth = 0;
        for (var i = text.Length - 1; i >= 0; i--) { if (text[i] == '>') depth++; if (text[i] == '<') depth--; if (text[i] == '.' && depth == 0) return i; }
        return -1;
    }
    private static string StripArity(string name) => name.Split('`')[0];
    public string GetTypeFromDefinition(MetadataReader r, TypeDefinitionHandle h, byte raw)
    {
        var t = r.GetTypeDefinition(h); var n = StripArity(r.GetString(t.Name));
        return t.IsNested ? GetTypeFromDefinition(r, t.GetDeclaringType(), 0) + "." + n : (r.GetString(t.Namespace) is { Length: > 0 } ns ? ns + "." : "") + n;
    }
    public string GetTypeFromReference(MetadataReader r, TypeReferenceHandle h, byte raw)
    {
        var t = r.GetTypeReference(h);
        var prefix = t.ResolutionScope.Kind == HandleKind.TypeReference ? GetTypeFromReference(r, (TypeReferenceHandle)t.ResolutionScope, raw) + "." :
            r.GetString(t.Namespace) is { Length: > 0 } ns ? ns + "." : "";
        return prefix + StripArity(r.GetString(t.Name));
    }
    public string GetTypeFromSpecification(MetadataReader r, GenericNames c, TypeSpecificationHandle h, byte raw) => r.GetTypeSpecification(h).DecodeSignature(this, c);
    public string GetArrayType(string e, ArrayShape shape) => e + "[" + new string(',', shape.Rank - 1) + "]";
    public string GetByReferenceType(string e) => e + "&";
    public string GetFunctionPointerType(MethodSignature<string> s) => "function-pointer";
    public string GetGenericInstantiation(string t, ImmutableArray<string> args) => t + "<" + string.Join(", ", args) + ">";
    public string GetGenericMethodParameter(GenericNames c, int i) => i < c.Methods.Length ? c.Methods[i] : "!!" + i;
    public string GetGenericTypeParameter(GenericNames c, int i) => i < c.Types.Length ? c.Types[i] : "!" + i;
    public string GetModifiedType(string m, string u, bool required) => u;
    public string GetPinnedType(string e) => e;
    public string GetPointerType(string e) => e + "*";
    public string GetPrimitiveType(PrimitiveTypeCode code) => "System." + code;
    public string GetSZArrayType(string e) => e + "[]";
    public void Dispose() { foreach (var dependency in dependencies.Values) dependency.Dispose(); pe.Dispose(); stream.Dispose(); }
}
