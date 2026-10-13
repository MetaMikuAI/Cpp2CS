using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Cpp2CS.Native;

// 样例范围来自定义清单；无入口和共享入口也保留，不能从分母中消失。
public static class NamespaceCorpus
{
    private sealed record Entry(string Id, string Assembly, string Namespace, string Type, string Name,
        string DefinitionToken, string? OriginalToken, ulong? Address, string Attributes, string Implementation,
        string[] NativeNames);
    private sealed record Request(string Id, ulong Address);
    private static readonly JsonSerializerOptions Json = new() { PropertyNamingPolicy = JsonNamingPolicy.CamelCase };
    private static string Hash(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexString(SHA256.HashData(stream)).ToLowerInvariant();
    }
    public static void Inventory(string configuration, string output, string[] namespaces)
    {
        if (namespaces.Length == 0) throw new ArgumentException("必须指定目标命名空间");
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!;
        using var symbols = JsonDocument.Parse(File.ReadAllText(inputs.Symbols));
        var native = symbols.RootElement.GetProperty("ScriptMethod").EnumerateArray()
            .GroupBy(m => m.GetProperty("Address").GetUInt64())
            .ToDictionary(g => g.Key, g => g.Select(m => m.GetProperty("Name").GetString()!).ToArray());
        var entries = new List<Entry>();
        var assemblies = new List<object>();
        foreach (var path in Directory.GetFiles(Path.GetDirectoryName(inputs.ManagedAssembly)!, "*.dll").Order(StringComparer.Ordinal))
        {
            using var stream = File.OpenRead(path);
            using var pe = new PEReader(stream);
            var reader = pe.GetMetadataReader();
            var before = entries.Count;
            string Namespace(TypeDefinitionHandle handle)
            {
                var type = reader.GetTypeDefinition(handle);
                return type.IsNested ? Namespace(type.GetDeclaringType()) : reader.GetString(type.Namespace);
            }
            string TypeName(TypeDefinitionHandle handle)
            {
                var type = reader.GetTypeDefinition(handle);
                return (type.IsNested ? TypeName(type.GetDeclaringType()) + "." : Namespace(handle) + ".") + reader.GetString(type.Name);
            }
            string AttributeName(CustomAttribute attribute)
            {
                var parent = attribute.Constructor.Kind == HandleKind.MemberReference
                    ? reader.GetMemberReference((MemberReferenceHandle)attribute.Constructor).Parent
                    : reader.GetMethodDefinition((MethodDefinitionHandle)attribute.Constructor).GetDeclaringType();
                return parent.Kind == HandleKind.TypeReference ? reader.GetString(reader.GetTypeReference((TypeReferenceHandle)parent).Name)
                    : reader.GetString(reader.GetTypeDefinition((TypeDefinitionHandle)parent).Name);
            }
            Dictionary<string, string?> Fields(CustomAttribute attribute)
            {
                var blob = reader.GetBlobReader(attribute.Value);
                if (blob.ReadUInt16() != 1) throw new InvalidDataException("属性编码无效");
                var count = blob.ReadUInt16();
                var fields = new Dictionary<string, string?>();
                for (var i = 0; i < count; i++)
                {
                    var kind = blob.ReadByte(); var type = blob.ReadByte();
                    if (kind is not (0x53 or 0x54) || type != 0x0e) throw new InvalidDataException("地址或 Token 属性不是字符串字段");
                    fields.Add(blob.ReadSerializedString()!, blob.ReadSerializedString());
                }
                return fields;
            }
            foreach (var handle in reader.TypeDefinitions)
            {
                var ns = Namespace(handle);
                if (!namespaces.Any(n => ns == n || ns.StartsWith(n + ".", StringComparison.Ordinal))) continue;
                var type = reader.GetTypeDefinition(handle);
                foreach (var methodHandle in type.GetMethods())
                {
                    var method = reader.GetMethodDefinition(methodHandle);
                    ulong? address = null;
                    string? originalToken = null;
                    foreach (var attributeHandle in method.GetCustomAttributes())
                    {
                        var attribute = reader.GetCustomAttribute(attributeHandle);
                        var name = AttributeName(attribute);
                        if (name == "AddressAttribute" && Fields(attribute).GetValueOrDefault("VA") is { } va)
                            address = Convert.ToUInt64(va.StartsWith("0x") ? va[2..] : va, 16);
                        if (name == "TokenAttribute") originalToken = Fields(attribute).GetValueOrDefault("Token");
                    }
                    if (address == 0) address = null;
                    var token = $"0x{MetadataTokens.GetToken(methodHandle):x8}";
                    entries.Add(new(Path.GetFileName(path) + ":" + token, Path.GetFileName(path), ns, TypeName(handle),
                        reader.GetString(method.Name), token, originalToken, address, method.Attributes.ToString(), method.ImplAttributes.ToString(),
                        address is { } pc ? native.GetValueOrDefault(pc, []) : []));
                }
            }
            if (entries.Count != before) assemblies.Add(new { name = Path.GetFileName(path), sha256 = Hash(path), methods = entries.Count - before });
        }
        // 泛型实例可能仅见于原生符号；单独保留，避免误称定义清单涵盖所有实例。
        var definitionAddresses = entries.Where(e => e.Address is not null).Select(e => e.Address!.Value).ToHashSet();
        var additionalSymbols = native.SelectMany(p => p.Value.Select(name => new { address = p.Key, name }))
            .Where(m => namespaces.Any(n => m.name.StartsWith(n + ".", StringComparison.Ordinal)) && !definitionAddresses.Contains(m.address)).ToArray();
        var manifest = new
        {
            schemaVersion = 1, namespaces,
            inputs = new { binarySha256 = Hash(inputs.Binary), metadataSha256 = inputs.Metadata is null ? null : Hash(inputs.Metadata),
                symbolsSha256 = Hash(inputs.Symbols), headerSha256 = Hash(inputs.Header) },
            assemblies, methods = entries, additionalSymbols,
            limitations = new[] { "DummyDLL and script are import evidence, not native semantic proof", "no native entry is not a recovered method", "shared VA does not establish managed identity" }
        };
        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(output))!);
        File.WriteAllText(output, JsonSerializer.Serialize(manifest, Json));
        Console.WriteLine(JsonSerializer.Serialize(new { methods = entries.Count, withAddress = entries.Count(e => e.Address is not null),
            uniqueAddresses = definitionAddresses.Count, additionalSymbols = additionalSymbols.Length,
            namespaces = entries.GroupBy(e => e.Namespace).Select(g => new { name = g.Key, count = g.Count() }) }, Json));
    }
    public static void Work(string configuration, string assembly, string output)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!;
        inputs = inputs with { ManagedAssembly = Path.Combine(Path.GetDirectoryName(inputs.ManagedAssembly)!, assembly) };
        using var session = new RecoverySession(inputs);
        Directory.CreateDirectory(output);
        Console.WriteLine("READY");
        while (Console.ReadLine() is { } line)
        {
            var request = JsonSerializer.Deserialize<Request>(line, Json)!;
            var candidates = session.Symbols.Methods.GetValueOrDefault(request.Address, []);
            if (candidates.Length != 1)
            {
                Console.WriteLine(JsonSerializer.Serialize(new { request.Id, request.Address,
                    status = candidates.Length == 0 ? "missing-native-signature" : "ambiguous-native-signature",
                    candidates = candidates.Select(m => m.Name) }, Json));
                continue;
            }
            var timer = System.Diagnostics.Stopwatch.StartNew();
            var result = session.Recover(request.Address);
            var text = session.Render(result);
            var file = $"0x{request.Address:x}.cs.txt";
            File.WriteAllText(Path.Combine(output, file), text);
            Console.WriteLine(JsonSerializer.Serialize(new
            {
                request.Id, request.Address, name = result.Method.Name,
                status = result.Problems.Count == 0 ? "no-reported-gaps" : "partial",
                route = result.Ssa?.Projection?.RecoveryPath ?? result.RecoveryPath,
                problems = result.Problems, ordinaryProblems = result.Ssa?.OrdinaryProblems,
                ssaProblems = result.Ssa?.Program.Problems, flowProblems = result.Ssa?.Program.Flow.Problems,
                asyncProblems = result.Ssa?.Body?.Problems, source = file,
                sourceSha256 = Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(text))).ToLowerInvariant(),
                elapsedMilliseconds = timer.ElapsedMilliseconds, runtimeValidated = false
            }, Json));
        }
    }
}
