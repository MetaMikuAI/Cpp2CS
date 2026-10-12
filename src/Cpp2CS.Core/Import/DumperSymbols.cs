using System.Text.Json;
using Cpp2CS.Model;

namespace Cpp2CS.Import;

// script.json 是符号提示，不包含构建完整类型实例和 ABI 所需的全部事实。
public sealed record MethodHint(NativeAddress Address, string Name, string? Signature);
public sealed record MetadataHint(NativeAddress Slot, string Category, string Name, string? Signature);
public sealed record DumperSymbols(Sequence<MethodHint> Methods, Sequence<MetadataHint> Metadata)
{
    public static DumperSymbols Read(Stream stream, BuildId build)
    {
        using var document = JsonDocument.Parse(stream);
        var methods = new List<MethodHint>();
        var metadata = new List<MetadataHint>();
        var root = document.RootElement;
        if (root.TryGetProperty("ScriptMethod", out var methodArray))
            foreach (var row in methodArray.EnumerateArray())
                methods.Add(new(new(build, row.GetProperty("Address").GetUInt64()), Text(row, "Name") ?? "", Text(row, "Signature")));
        foreach (var category in new[] { "ScriptMetadata", "ScriptMetadataMethod", "ScriptString" })
            if (root.TryGetProperty(category, out var rows))
                foreach (var row in rows.EnumerateArray())
                    metadata.Add(new(new(build, row.GetProperty("Address").GetUInt64()), category,
                        Text(row, "Name") ?? Text(row, "Value") ?? "", Text(row, "Signature")));
        return new(new(methods), new(metadata));
    }
    private static string? Text(JsonElement row, string property) => row.TryGetProperty(property, out var value) ? value.GetString() : null;
}
