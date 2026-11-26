using System.Text.Json;

namespace Cpp2CS.Spec.Runtime;

/// <summary>直接边保留体内字节位置和目标名称。无名或目标名称不唯一的边不能闭合。</summary>
public sealed record FingerprintEdge(int Offset, string? Name)
{
    /// <summary>有符号但不能作为运行时身份的落点，保留其全部名字供诊断。</summary>
    [System.Text.Json.Serialization.JsonIgnore(Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
    public string[]? ExcludedNames { get; init; }
}
public sealed record DataReference(int Offset, string Kind, long Displacement, string? Sha256);
public sealed record FingerprintBody(int Length, string Sha256, DataReference[] Data, bool Comparable);
public sealed record FingerprintRow(string[] Names, FingerprintBody Body, FingerprintEdge[] Edges, bool Registered);

/// <summary>参照来自与原生映像构建标识相同的符号文件。格式只保存内容摘要。</summary>
public sealed record RuntimeFingerprint(int Format, string BuildId, string SymbolsSha256, string Target,
    string RuntimeVersion, string Toolchain, FingerprintRow[] Rows)
{
    public static RuntimeFingerprint Read(string path)
    {
        using var stream = File.OpenRead(path);
        var table = JsonSerializer.Deserialize<RuntimeFingerprint>(stream) ?? throw new InvalidDataException("指纹表为空");
        static bool Hash(string? s) => s is { Length: 64 } && s.All(Uri.IsHexDigit);
        if (table.Format != 1 || string.IsNullOrEmpty(table.BuildId) || !table.BuildId.All(Uri.IsHexDigit) ||
            !Hash(table.SymbolsSha256) || string.IsNullOrWhiteSpace(table.RuntimeVersion) ||
            string.IsNullOrWhiteSpace(table.Toolchain) || string.IsNullOrEmpty(table.Target) || table.Rows == null)
            throw new InvalidDataException("指纹表头无效");
        foreach (var row in table.Rows)
        {
            if (row is not { Body: { } b, Names: not null, Edges: not null } || b.Data == null ||
                b.Length < 0 || (b.Length & 3) != 0 || !Hash(b.Sha256) || b.Comparable && b.Length == 0 ||
                row.Names.Any(string.IsNullOrEmpty) || row.Names.Distinct().Count() != row.Names.Length)
                throw new InvalidDataException("指纹行无效");
            bool At(int at) => at >= 0 && at < b.Length && at % 4 == 0;
            if (row.Edges.Any(e => e == null || !At(e.Offset) || e.Name is { Length: 0 } ||
                    e.ExcludedNames != null && (e.Name != null || e.ExcludedNames.Any(string.IsNullOrEmpty))) ||
                !row.Edges.Select(e => e.Offset).SequenceEqual(row.Edges.Select(e => e.Offset).Distinct().Order()) ||
                b.Data.Any(d => d == null || !At(d.Offset) || d.Kind switch
                {
                    "可写" => d.Sha256 != null || d.Displacement != 0,
                    "只读" => !Hash(d.Sha256),
                    _ => true
                }))
                throw new InvalidDataException("指纹边或数据引用无效");
        }
        return table;
    }

    public void Write(string path)
    {
        string directory = Path.GetDirectoryName(Path.GetFullPath(path))!;
        Directory.CreateDirectory(directory);
        string temporary = Path.Combine(directory, Guid.NewGuid().ToString("N") + ".local.tmp");
        try
        {
            using (var stream = new FileStream(temporary, FileMode.CreateNew, FileAccess.Write, FileShare.None))
                JsonSerializer.Serialize(stream, this);
            File.Move(temporary, path, overwrite: true);
        }
        finally { File.Delete(temporary); }
    }
}
