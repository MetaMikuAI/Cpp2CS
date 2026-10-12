using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;

namespace Cpp2CS.Native;

public sealed record InterfaceMethod(string Type, int Slot, string Name, string ReturnType, string[] ParameterTypes);
public sealed record AsyncSource(string Owner, string Name, string ReturnType, string[] ParameterTypes, string[] ParameterNames, bool Static);

public sealed partial class ManagedNames
{
    private readonly Dictionary<string, ManagedNames?> exportedDefinitions = [];
    public string? MutableField(string typeName, string nativeName, bool publicOnly = false)
    {
        var (name, arguments) = SplitGeneric(typeName);
        var owner = FindDefinition(name);
        var handle = owner?.DefinitionWithArity(name, arguments.Length) ?? default;
        if (owner is null || handle.IsNil) return null;
        static string Encode(string text) => System.Text.RegularExpressions.Regex.Replace(text, @"[^a-zA-Z0-9_]", "_");
        var definition = owner.reader.GetTypeDefinition(handle);
        var fields = definition.GetFields().Select(owner.reader.GetFieldDefinition)
            .Where(f => Encode(owner.reader.GetString(f.Name)) == nativeName &&
                (f.Attributes & (FieldAttributes.InitOnly | FieldAttributes.Literal | FieldAttributes.Static)) == 0).ToArray();
        if (fields.Length != 1) return null;
        var field = fields[0]; var fieldName = owner.reader.GetString(field.Name);
        if (fieldName == nativeName) return !publicOnly || (field.Attributes & FieldAttributes.FieldAccessMask) == FieldAttributes.Public ? fieldName : null;
        if (!fieldName.StartsWith('<') || !fieldName.EndsWith(">k__BackingField")) return null;
        var propertyName = fieldName[1..fieldName.IndexOf('>')];
        var setters = definition.GetProperties().Select(owner.reader.GetPropertyDefinition).Where(p => owner.reader.GetString(p.Name) == propertyName)
            .Select(p => p.GetAccessors().Setter).Where(h => !h.IsNil).Select(owner.reader.GetMethodDefinition).ToArray();
        return setters.Length == 1 && (!publicOnly || (setters[0].Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public) &&
            (setters[0].Attributes & MethodAttributes.Virtual) == 0 &&
            setters[0].GetCustomAttributes().Select(owner.AttributeName).Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute") ? propertyName : null;
    }
    public bool HasDefaultValueConstruction(string typeName)
    {
        if (BaseTypeOf(typeName) != "System.ValueType") return false;
        var (name, arguments) = SplitGeneric(typeName); var owner = FindDefinition(name)!;
        var handle = owner.DefinitionWithArity(name, arguments.Length);
        return !owner.reader.GetTypeDefinition(handle).GetMethods().Select(owner.reader.GetMethodDefinition).Any(m =>
            owner.reader.GetString(m.Name) == ".ctor" && m.DecodeSignature(owner, new GenericNames(arguments, [])).ParameterTypes.Length == 0);
    }
    public (string Name, string Type)? SourceMember(string type, string nativeName)
    {
        var (name, arguments) = SplitGeneric(type);
        var owner = FindDefinition(name);
        var handle = owner?.DefinitionWithArity(name, arguments.Length) ?? default;
        if (owner is null || handle.IsNil) return null;
        var definition = owner.reader.GetTypeDefinition(handle);
        static string Encode(string text) => System.Text.RegularExpressions.Regex.Replace(text, @"[^a-zA-Z0-9_]", "_");
        var fields = definition.GetFields().Select(owner.reader.GetFieldDefinition).Where(f => Encode(owner.reader.GetString(f.Name)) == nativeName).ToArray();
        if (fields.Length != 1) return null;
        var field = fields[0]; var fieldName = owner.reader.GetString(field.Name);
        var fieldType = field.DecodeSignature(owner, new GenericNames(arguments, []));
        if (fieldName.StartsWith('<') && fieldName.EndsWith(">k__BackingField"))
        {
            var propertyName = fieldName[1..fieldName.IndexOf('>')];
            var property = definition.GetProperties().Select(owner.reader.GetPropertyDefinition).Where(p => owner.reader.GetString(p.Name) == propertyName).ToArray();
            if (property.Length != 1 || property[0].GetAccessors().Getter.IsNil) return null;
            if (!owner.reader.GetMethodDefinition(property[0].GetAccessors().Getter).GetCustomAttributes().Select(owner.AttributeName)
                .Contains("System.Runtime.CompilerServices.CompilerGeneratedAttribute")) return null;
            return (propertyName, fieldType);
        }
        return (fieldName, fieldType);
    }
    public string[] GenericParameterNames(string type)
    {
        var (name, arguments) = SplitGeneric(type);
        var owner = FindDefinition(name);
        var handle = owner?.DefinitionWithArity(name, arguments.Length) ?? default;
        return owner is null || handle.IsNil ? [] : owner.reader.GetTypeDefinition(handle).GetGenericParameters()
            .Select(h => owner.reader.GetString(owner.reader.GetGenericParameter(h).Name)).ToArray();
    }
    private TypeDefinitionHandle DefinitionWithArity(string name, int arity) => reader.TypeDefinitions.FirstOrDefault(h =>
        GetTypeFromDefinition(reader, h, 0) == name && reader.GetTypeDefinition(h).GetGenericParameters().Count == arity);
    public string? BindEncodedContextType(string encoded, string context)
    {
        var (name, arguments) = SplitGeneric(context);
        var owner = FindDefinition(name);
        if (owner is null) return null;
        var parameters = GenericParameterNames(context);
        if (parameters.Length != arguments.Length) return null;
        static string Encode(string text) => System.Text.RegularExpressions.Regex.Replace(text, @"[^a-zA-Z0-9_]", "_");
        var matches = new List<string>();
        foreach (var handle in owner.reader.TypeDefinitions)
        {
            var typeName = owner.GetTypeFromDefinition(owner.reader, handle, 0);
            var count = owner.reader.GetTypeDefinition(handle).GetGenericParameters().Count;
            if (count == 0 && Encode(typeName) == encoded) matches.Add(typeName);
            if (count != 1) continue;
            for (var i = 0; i < parameters.Length; i++)
                if (Encode(typeName + "<" + parameters[i] + ">") == encoded) matches.Add(typeName + "<" + arguments[i] + ">");
        }
        for (var i = 0; i < parameters.Length; i++) if (Encode(parameters[i]) == encoded) matches.Add(arguments[i]);
        var distinct = matches.Distinct().ToArray();
        return distinct.Length == 1 ? distinct[0] : null;
    }
    private ManagedNames? FindDefinition(string name)
    {
        if (types.ContainsKey(name)) return this;
        foreach (var handle in reader.TypeReferences)
        {
            if (GetTypeFromReference(reader, handle, 0) != name) continue;
            var scope = reader.GetTypeReference(handle).ResolutionScope;
            while (scope.Kind == HandleKind.TypeReference) scope = reader.GetTypeReference((TypeReferenceHandle)scope).ResolutionScope;
            if (scope.Kind != HandleKind.AssemblyReference) return null;
            var assembly = reader.GetString(reader.GetAssemblyReference((AssemblyReferenceHandle)scope).Name);
            if (!dependencies.TryGetValue(assembly, out var dependency))
            {
                var path = Path.Combine(directory, assembly + ".dll");
                if (!File.Exists(path)) return null;
                dependencies.Add(assembly, dependency = new(path));
            }
            return dependency.types.ContainsKey(name) ? dependency : null;
        }
        foreach (var reference in reader.AssemblyReferences)
        {
            var assembly = reader.GetString(reader.GetAssemblyReference(reference).Name);
            if (dependencies.TryGetValue(assembly, out var loaded))
            { if (loaded.types.ContainsKey(name)) return loaded; continue; }
            var path = Path.Combine(directory, assembly + ".dll");
            if (!File.Exists(path)) continue;
            using var stream = File.OpenRead(path);
            using var pe = new PEReader(stream);
            var metadata = pe.GetMetadataReader();
            if (!metadata.TypeDefinitions.Any(h => GetTypeFromDefinition(metadata, h, 0) == name)) continue;
            dependencies.Add(assembly, loaded = new(path));
            return loaded;
        }
        // Dumper 的占位方法体可能不保留原程序集引用；仅接受同一导出目录中的唯一类型定义。
        if (exportedDefinitions.TryGetValue(name, out var cached)) return cached;
        var matches = new List<string>();
        foreach (var path in Directory.EnumerateFiles(directory, "*.dll"))
        {
            using var file = File.OpenRead(path);
            using var candidate = new PEReader(file);
            if (!candidate.HasMetadata) continue;
            var metadata = candidate.GetMetadataReader();
            if (metadata.TypeDefinitions.Any(h => GetTypeFromDefinition(metadata, h, 0) == name)) matches.Add(path);
        }
        if (matches.Count != 1) { exportedDefinitions[name] = null; return null; }
        var key = Path.GetFileNameWithoutExtension(matches[0]);
        if (!dependencies.TryGetValue(key, out var resolved)) dependencies.Add(key, resolved = new(matches[0]));
        exportedDefinitions[name] = resolved;
        return resolved;
    }
    public InterfaceMethod? InterfaceSlot(string typeName, int slot)
    {
        var (name, arguments) = SplitGeneric(typeName);
        var owner = FindDefinition(name);
        if (owner is null) return null;
        var handle = owner.DefinitionWithArity(name, arguments.Length);
        if (handle.IsNil) return null;
        var definition = owner.reader.GetTypeDefinition(handle);
        if ((definition.Attributes & TypeAttributes.Interface) == 0) return null;
        // IL2CPP 接口偏移指向本接口声明的方法序列，继承接口有各自的偏移项。
        var methods = definition.GetMethods().Select(owner.reader.GetMethodDefinition).Where(m => (m.Attributes & MethodAttributes.Static) == 0).ToArray();
        if (slot < 0 || slot >= methods.Length || methods.Any(m => (m.Attributes & MethodAttributes.Virtual) == 0)) return null;
        var signature = methods[slot].DecodeSignature(owner, new GenericNames(arguments, []));
        return new(typeName, slot, owner.reader.GetString(methods[slot].Name), signature.ReturnType, signature.ParameterTypes.ToArray());
    }
    private string EntityName(EntityHandle handle) => handle.Kind switch
    {
        HandleKind.TypeDefinition => GetTypeFromDefinition(reader, (TypeDefinitionHandle)handle, 0),
        HandleKind.TypeReference => GetTypeFromReference(reader, (TypeReferenceHandle)handle, 0),
        HandleKind.TypeSpecification => GetTypeFromSpecification(reader, new([], []), (TypeSpecificationHandle)handle, 0),
        _ => ""
    };
    private string AttributeName(CustomAttributeHandle handle)
    {
        var constructor = reader.GetCustomAttribute(handle).Constructor;
        return constructor.Kind == HandleKind.MemberReference ? EntityName(reader.GetMemberReference((MemberReferenceHandle)constructor).Parent) :
            constructor.Kind == HandleKind.MethodDefinition ? EntityName(reader.GetMethodDefinition((MethodDefinitionHandle)constructor).GetDeclaringType()) : "";
    }
    public bool Implements(string name, string contract)
    {
        var (root, _) = SplitGeneric(name);
        var owner = FindDefinition(root);
        return owner is not null && owner.types.TryGetValue(root, out var handle) && owner.reader.GetTypeDefinition(handle).GetInterfaceImplementations()
            .Any(h => owner.EntityName(owner.reader.GetInterfaceImplementation(h).Interface) == contract);
    }
    public AsyncSource[] SourcesFor(string stateType)
    {
        var result = new List<AsyncSource>();
        foreach (var handle in reader.MethodDefinitions)
        {
            var method = reader.GetMethodDefinition(handle);
            foreach (var attribute in method.GetCustomAttributes())
            {
                if (AttributeName(attribute) != "System.Runtime.CompilerServices.AsyncStateMachineAttribute") continue;
                var blob = reader.GetBlobReader(reader.GetCustomAttribute(attribute).Value);
                if (blob.ReadUInt16() != 1 || blob.ReadSerializedString() is not { } linked || linked.Split(',')[0].Replace('+', '.') != stateType) continue;
                var signature = method.DecodeSignature(this, new GenericNames([], []));
                var parameters = method.GetParameters().Select(reader.GetParameter).Where(p => p.SequenceNumber != 0).OrderBy(p => p.SequenceNumber).Select(p => reader.GetString(p.Name)).ToArray();
                result.Add(new(EntityName(method.GetDeclaringType()), reader.GetString(method.Name), signature.ReturnType, signature.ParameterTypes.ToArray(), parameters, (method.Attributes & MethodAttributes.Static) != 0));
            }
        }
        return result.ToArray();
    }
}
