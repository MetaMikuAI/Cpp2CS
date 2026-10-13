using System.Text.Json;
using System.Text.RegularExpressions;

namespace Cpp2CS.Native;

public sealed record NativeParameter(string Type, string Name);
public sealed record NativeMethod(ulong Address, string Name, string ReturnType, NativeParameter[] Parameters, string Signature);
public sealed record MetadataReference(ulong Slot, string Kind, string Name, string Type, ulong MethodAddress);
public sealed class Symbols
{
    public Dictionary<ulong, NativeMethod[]> Methods { get; }
    public Dictionary<string, NativeMethod[]> NamedMethods { get; }
    public Dictionary<ulong, MetadataReference> Metadata { get; } = [];
    public Dictionary<string, string> DisplayTypes { get; } = [];
    public ulong[] Entries { get; }
    private Symbols(Symbols source)
    {
        Methods = source.Methods; NamedMethods = source.NamedMethods; Metadata = source.Metadata; Entries = source.Entries;
        DisplayTypes = new(source.DisplayTypes);
    }
    // 元数据只读共享；分析期间发现的类型别名只属于当前方法。
    public Symbols ForMethod() => new(this);
    public Symbols(string path)
    {
        using var stream = File.OpenRead(path);
        using var document = JsonDocument.Parse(stream);
        var methods = new List<NativeMethod>();
        var entries = new HashSet<ulong>();
        foreach (var row in document.RootElement.GetProperty("ScriptMethod").EnumerateArray())
        {
            entries.Add(row.GetProperty("Address").GetUInt64());
            var signature = row.GetProperty("Signature").GetString()!;
            var match = Regex.Match(signature, @"^(.+?)\s+\w+\s*\((.*)\);$");
            if (!match.Success) continue;
            var parameters = new List<NativeParameter>();
            foreach (var parameter in match.Groups[2].Value.Split(','))
            {
                if (parameter.Trim() is "" or "void") continue;
                var p = Regex.Match(parameter.Trim(), @"^(.+?[\s*])(\w+)$");
                if (!p.Success)
                    parameters.Add(new(Clean(parameter.Trim()), "arg" + parameters.Count));
                else parameters.Add(new(Clean(p.Groups[1].Value), p.Groups[2].Value));
            }
            var name = row.GetProperty("Name").GetString()!;
            var method = new NativeMethod(row.GetProperty("Address").GetUInt64(), name, Clean(match.Groups[1].Value), parameters.ToArray(), signature);
            methods.Add(method);
            if (parameters.FirstOrDefault() is { Name: "__this" } receiver)
                DisplayTypes.TryAdd(receiver.Type.TrimEnd('*'), name.Split("$$")[0]);
        }
        Methods = methods.GroupBy(m => m.Address).ToDictionary(g => g.Key, g => g.ToArray());
        NamedMethods = methods.GroupBy(m => m.Name).ToDictionary(g => g.Key, g => g.ToArray());
        Entries = entries.Order().ToArray();
        foreach (var key in new[] { "ScriptMetadata", "ScriptMetadataMethod", "ScriptString" })
            if (document.RootElement.TryGetProperty(key, out var array))
                foreach (var row in array.EnumerateArray())
                {
                    var address = row.GetProperty("Address").GetUInt64();
                    var name = row.TryGetProperty("Name", out var n) ? n.GetString()! : row.GetProperty("Value").GetString()!;
                    var type = row.TryGetProperty("Signature", out var s) && s.ValueKind == JsonValueKind.String ? Clean(s.GetString()!) : "";
                    var reference = new MetadataReference(address, key, name, type, row.TryGetProperty("MethodAddress", out var ma) ? ma.GetUInt64() : 0);
                    if (!Metadata.TryAdd(address, reference) && Metadata[address] != reference) throw new InvalidDataException("冲突元数据槽");
                    if (key == "ScriptMetadata" && name.EndsWith("_TypeInfo") && type.EndsWith("_c*"))
                        DisplayTypes.TryAdd(type[..^3] + "_o", name[..^9]);
                }
    }
    public static string Clean(string type) => Regex.Replace(Regex.Replace(type, @"\b(const|struct|union|volatile)\b", ""), @"\s+", " ").Trim().Replace(" *", "*");
    public NativeMethod? Unique(ulong address) => Methods.TryGetValue(address, out var methods) && methods.Length == 1 ? methods[0] : null;
    public ulong Ceiling(ulong address)
    {
        var i = Array.BinarySearch(Entries, address);
        if (i < 0 || i + 1 >= Entries.Length) throw new InvalidDataException("缺少入口边界符号");
        return Entries[i + 1];
    }
    public string Display(string type)
    {
        var root = type.TrimEnd('*');
        if (root == "Il2CppObject") return "object";
        if (DisplayTypes.TryGetValue(root, out var name)) return name;
        return root switch { "void" => "void", "bool" => "bool", "int32_t" => "int", "int64_t" => "long", "System_String_o" => "string", _ => root };
    }
    public string? NativeType(string type)
    {
        var primitive = type switch { "System.Void" => "void", "System.Boolean" or "bool" => "bool", "System.Int32" or "int" => "int32_t", "System.Int16" => "int16_t", "System.Single" => "float", "System.String" or "string" => "System_String_o*", _ => null };
        if (primitive is not null) return primitive;
        var candidates = DisplayTypes.Where(p => p.Value == type).Select(p => p.Key).Distinct().ToArray();
        return candidates.Length == 1 ? candidates[0] : null;
    }
}
