using System.Text.Json;
using System.Text.Json.Serialization;

namespace Cpp2CS.Spec.Runtime;

[JsonConverter(typeof(JsonStringEnumConverter<ReferenceKind>))]
public enum ReferenceKind { Code, ReadOnly, Writable, Outside }

public sealed record FingerprintReference(int Offset, ReferenceKind Kind, ulong Target, string? Digest = null);
public sealed record FingerprintBody(int Length, string Sha256, FingerprintReference[] References, bool Comparable)
{
    // 只读内容和节内偏移属于值；代码和可写地址只在配对之后核对。表外仍保留代码位置。
    [JsonIgnore]
    public string LocalKey => $"{Length}/{Sha256}/" + string.Join(',', References.Select(r => r.Kind switch
    {
        ReferenceKind.ReadOnly => $"{r.Offset}:r:{r.Target}:{r.Digest}",
        ReferenceKind.Writable => $"{r.Offset}:w",
        _ => $"{r.Offset}:c"
    }));
}

public sealed record FingerprintRow(ulong Address, string[] Names, FingerprintBody Body, ulong Class);
public sealed record ImportAnchor(ulong Address, string Name);

/// <summary>参照行只来自运行时编译单元。导入桩单独按重定位登记，不充当运行时函数体。</summary>
public sealed record RuntimeFingerprint(int Format, string BuildId, string SymbolsSha256, string DebugSha256, string Target,
    string RuntimeVersion, string Toolchain, FingerprintRow[] Rows, ImportAnchor[] Imports, ulong[] UnclassifiedCode)
{
    public static FingerprintRow[] Partition(FingerprintRow[] rows, ImportAnchor[] imports)
    {
        var importClasses = imports.GroupBy(i => i.Name).SelectMany(g => g.Select(i => (i.Address, Class: g.Min(x => x.Address))))
            .ToDictionary(i => i.Address, i => i.Class);
        var colors = rows.ToDictionary(r => r.Address, _ => 0ul);
        // 不可比函数只能自成一类。其调用者仍然可以按目标类划分。
        var keys = rows.ToDictionary(r => r.Address, r => r.Body.Comparable ? r.Body.LocalKey + "/" +
            string.Join(',', r.Body.References.Where(e => e.Kind is ReferenceKind.Writable or ReferenceKind.Outside)
                .Select(e => $"{e.Offset}:{e.Kind}:{e.Target}")) : $"?{r.Address}");
        while (true)
        {
            var groups = rows.GroupBy(r => keys[r.Address] + "/" + string.Join(',', r.Body.References
                .Where(e => e.Kind == ReferenceKind.Code).Select(e => colors.GetValueOrDefault(e.Target, importClasses.GetValueOrDefault(e.Target, e.Target)))));
            var next = new Dictionary<ulong, ulong>();
            foreach (var group in groups)
            {
                ulong id = group.Min(r => r.Address);
                foreach (var row in group) next.Add(row.Address, id);
            }
            if (rows.All(r => colors[r.Address] == next[r.Address])) break;
            colors = next;
        }
        return rows.Select(r => r with { Class = colors[r.Address] }).ToArray();
    }

    public static RuntimeOperation? RegisteredOperation(IEnumerable<string> names)
    {
        var ops = names.Select(RuntimeOperations.BySymbol).OfType<RuntimeOperation>().Distinct().ToArray();
        if (ops.Length > 1) throw new InvalidDataException($"同一参照类有不同操作：{string.Join('、', ops.Select(o => o.Id))}");
        return ops.SingleOrDefault();
    }

    private void Validate()
    {
        static bool Hash(string? s) => s is { Length: 64 } && s.All(Uri.IsHexDigit);
        if (Format != 2 || string.IsNullOrEmpty(BuildId) || !BuildId.All(Uri.IsHexDigit) ||
            !Hash(SymbolsSha256) || !Hash(DebugSha256) || string.IsNullOrWhiteSpace(RuntimeVersion) ||
            string.IsNullOrWhiteSpace(Toolchain) || string.IsNullOrWhiteSpace(Target) || Rows == null || Imports == null || UnclassifiedCode == null)
            throw new InvalidDataException("指纹表头无效");
        var addresses = new HashSet<ulong>();
        foreach (ulong address in UnclassifiedCode)
            if (!addresses.Add(address)) throw new InvalidDataException("缺编译单元的目标地址重复");
        foreach (var import in Imports)
            if (import == null || !addresses.Add(import.Address) || string.IsNullOrEmpty(import.Name))
                throw new InvalidDataException("导入锚点无效");
        foreach (var row in Rows)
            if (row is not { Body: { References: not null } b, Names: not null } || !addresses.Add(row.Address) ||
                b.Length < 0 || b.Length % 4 != 0 || !Hash(b.Sha256) || b.Comparable && b.Length == 0 ||
                row.Names.Any(string.IsNullOrEmpty) || row.Names.Distinct().Count() != row.Names.Length)
                throw new InvalidDataException("指纹行无效");
        foreach (var row in Rows)
        {
            int previous = -1;
            foreach (var r in row.Body.References)
            {
                if (r == null || r.Offset <= previous || r.Offset >= row.Body.Length || r.Offset % 4 != 0 ||
                    !Enum.IsDefined(r.Kind) || (r.Kind == ReferenceKind.ReadOnly ? !Hash(r.Digest) : r.Digest != null) ||
                    r.Kind == ReferenceKind.Code && !addresses.Contains(r.Target) || r.Kind == ReferenceKind.Outside && r.Target != 0)
                    throw new InvalidDataException("指纹引用无效");
                previous = r.Offset;
            }
        }
        if (!Partition(Rows, Imports).Select(r => r.Class).SequenceEqual(Rows.Select(r => r.Class)))
            throw new InvalidDataException("参照类与划分不一致");
        foreach (var group in Rows.GroupBy(r => r.Class)) RegisteredOperation(group.SelectMany(r => r.Names));
    }

    public static RuntimeFingerprint Read(string path)
    {
        using var stream = File.OpenRead(path);
        var table = JsonSerializer.Deserialize<RuntimeFingerprint>(stream) ?? throw new InvalidDataException("指纹表为空");
        table.Validate();
        return table;
    }

    public void Write(string path)
    {
        Validate();
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
