using System.Text.Json;

namespace Cpp2CS.Runtime;

public sealed record RuntimeCalleeShape(ulong Length, string Shape)
{
    public string[] Functions { get; init; } = [];
    [System.Text.Json.Serialization.JsonIgnore(Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
    public RuntimeCalleeShape[]? Callees { get; init; }
}
public sealed record RuntimeShapeEntry(string Function, ulong Length, string Shape, RuntimeCalleeShape[] Callees)
{
    public bool HasImportCalls { get; init; }
}
public sealed record RuntimeShapeMissing(string Function, string Reason);
/// <summary>同版本同目标构建的离线形状；不保存参考映像的地址。</summary>
public sealed record RuntimeShapeCatalog(int FormatVersion, string UnityVersion, string Triple, string DataModel, RuntimeShapeEntry[] Entries)
{
    public RuntimeShapeMissing[] Missing { get; init; } = [];
    public string? ReferenceImageSha256 { get; init; }
    public string? ReferenceSymbolsSha256 { get; init; }
    public static JsonSerializerOptions JsonOptions => new() { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower, WriteIndented = true };

    public static RuntimeShapeCatalog? Select(string unityVersion, string triple, string dataModel)
    {
        var assembly = typeof(RuntimeShapeCatalog).Assembly;
        var candidates = new List<RuntimeShapeCatalog>();
        foreach (var name in assembly.GetManifestResourceNames().Where(n => n.StartsWith("Cpp2CS.Shapes.", StringComparison.Ordinal)))
        {
            using var stream = assembly.GetManifestResourceStream(name)!;
            var data = JsonSerializer.Deserialize<RuntimeShapeCatalog>(stream, JsonOptions) ?? throw new InvalidDataException("形状目录为空");
            if (data.FormatVersion != 1) throw new InvalidDataException("未知形状目录版本");
            if (data.UnityVersion == unityVersion && data.Triple == triple && data.DataModel == dataModel) candidates.Add(data);
        }
        return candidates.Count switch { 0 => null, 1 => candidates[0], _ => throw new InvalidDataException("形状目录不唯一") };
    }
}
