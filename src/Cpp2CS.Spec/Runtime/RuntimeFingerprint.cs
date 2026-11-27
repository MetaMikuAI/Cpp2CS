using System.Text.Json;
using System.Text.Json.Serialization;

namespace Cpp2CS.Spec.Runtime;

[JsonConverter(typeof(JsonStringEnumConverter<ReferenceKind>))]
public enum ReferenceKind { Code, ReadOnly, Writable, Outside, Import }

public sealed record FingerprintBinding(string Symbol, ulong Addend, string Identity);

public sealed record FingerprintReference(int Offset, ReferenceKind Kind, ulong Target, string? Digest = null)
{
    // 指令所引只读对象内的重定位，逐级记录相对对象起点的字节偏移。
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
    public string? Path { get; init; }
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
    public FingerprintBinding? Binding { get; init; }
}
public sealed record FingerprintBody(int Length, string Sha256, FingerprintReference[] References, bool Comparable)
{
    // 只读内容和节内偏移属于值；代码和可写地址只在配对之后核对。表外仍保留代码位置。
    [JsonIgnore]
    public string LocalKey => $"{Length}/{Sha256}/" + string.Join(',', References.Select(r => $"{r.Offset}{r.Path}:" +
        (r.Binding is { } b ? $"{b.Symbol.Length}:{b.Symbol}:{b.Addend}:{b.Identity}:" : "") + (r.Kind switch
    {
        ReferenceKind.ReadOnly => $"r:{r.Target}:{r.Digest}",
        ReferenceKind.Writable => "w",
        ReferenceKind.Import => "i",
        _ => "c"
    })));
}

public sealed record FingerprintRow(ulong Address, string[] Names, FingerprintBody Body, ulong Class, bool Runtime);
public sealed record ImportAnchor(ulong Address, string Name);

/// <summary>全映像参与划分。只有运行时编译单元的行可以供名；导入桩按重定位单独登记。</summary>
public sealed record RuntimeFingerprint(int Format, string BuildId, string SymbolsSha256, string DebugSha256, string Target,
    string RuntimeVersion, string Toolchain, FingerprintRow[] Rows, ImportAnchor[] Imports)
{
    public static FingerprintRow[] Partition(FingerprintRow[] rows, ImportAnchor[] imports)
    {
        var importClasses = imports.GroupBy(i => i.Name).SelectMany(g => g.Select(i => (i.Address, Class: g.Min(x => x.Address))))
            .ToDictionary(i => i.Address, i => i.Class);
        var colors = rows.ToDictionary(r => r.Address, _ => 0ul);
        // 不可比函数只能自成一类。其调用者仍然可以按目标类划分。
        var keys = rows.ToDictionary(r => r.Address, r => r.Body.Comparable ? r.Body.LocalKey + "/" +
            string.Join(',', r.Body.References.Where(e => e.Kind is ReferenceKind.Writable or ReferenceKind.Outside)
                .Select(e => $"{e.Offset}{e.Path}:{e.Kind}:{e.Target}")) : $"?{r.Address}");
        while (true)
        {
            var groups = rows.GroupBy(r => (r.Runtime, Key: keys[r.Address] + "/" + string.Join(',', r.Body.References
                .Where(e => e.Kind == ReferenceKind.Code).Select(e => colors.GetValueOrDefault(e.Target, importClasses.GetValueOrDefault(e.Target, e.Target))))));
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
        RuntimeOperation? operation = null;
        foreach (string name in names)
        {
            var entry = RuntimeOperations.BySymbol(name);
            if (entry == null || operation != null && operation != entry) return null;
            operation = entry;
        }
        return operation;
    }

    private void Validate()
    {
        static bool Hash(string? s) => s is { Length: 64 } && s.All(Uri.IsHexDigit);
        if (Format != 4) throw new InvalidDataException("参照表需要带数据重定位的局部指纹，请重新建表");
        if (string.IsNullOrEmpty(BuildId) || !BuildId.All(Uri.IsHexDigit) ||
            !Hash(SymbolsSha256) || !Hash(DebugSha256) || string.IsNullOrWhiteSpace(RuntimeVersion) ||
            string.IsNullOrWhiteSpace(Toolchain) || string.IsNullOrWhiteSpace(Target) || Rows == null || Imports == null)
            throw new InvalidDataException("指纹表头无效");
        var addresses = new HashSet<ulong>();
        foreach (var import in Imports)
            if (import == null || !addresses.Add(import.Address) || string.IsNullOrEmpty(import.Name))
                throw new InvalidDataException("导入锚点无效");
        foreach (var row in Rows)
            if (row is not { Body: { References: not null } b, Names: not null } || !addresses.Add(row.Address) ||
                b.Length < 0 || b.Length % 4 != 0 || !Hash(b.Sha256) || b.Comparable && b.Length == 0 ||
                !row.Runtime && row.Names.Length != 0 || row.Names.Any(string.IsNullOrEmpty) || row.Names.Distinct().Count() != row.Names.Length)
                throw new InvalidDataException("指纹行无效");
        foreach (var row in Rows)
        {
            int previous = -1;
            string? path = null;
            var objects = new HashSet<string>();
            foreach (var r in row.Body.References)
            {
                if (r == null || r.Offset < 0 || r.Offset < previous || r.Offset >= row.Body.Length || r.Offset % 4 != 0 ||
                    !Enum.IsDefined(r.Kind) || (r.Kind == ReferenceKind.ReadOnly ? !Hash(r.Digest) : r.Digest != null) ||
                    r.Binding is { } binding && (r.Path == null || string.IsNullOrEmpty(binding.Symbol) || !Hash(binding.Identity)) ||
                    r.Kind == ReferenceKind.Import && (r.Binding == null || r.Target != 0) ||
                    r.Kind == ReferenceKind.Code && !addresses.Contains(r.Target) || r.Kind == ReferenceKind.Outside && r.Target != 0)
                    throw new InvalidDataException("指纹引用无效");
                if (previous != r.Offset)
                {
                    if (r.Path != null) throw new InvalidDataException("数据引用缺少根");
                    objects.Clear();
                }
                else if (r.Path is not { Length: >= 9 } p || string.CompareOrdinal(path, p) >= 0 ||
                    p[^9] != '/' || !p[^8..].All(Uri.IsHexDigit) || !objects.Contains(p[..^9]))
                    throw new InvalidDataException("数据引用路径无效");
                if (r.Kind == ReferenceKind.ReadOnly) objects.Add(r.Path ?? "");
                path = r.Path;
                previous = r.Offset;
            }
        }
        if (!Partition(Rows, Imports).Select(r => r.Class).SequenceEqual(Rows.Select(r => r.Class)))
            throw new InvalidDataException("参照类与划分不一致");
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
        foreach (var group in Rows.Where(r => r.Runtime).GroupBy(r => r.Class))
        {
            var operations = group.SelectMany(r => r.Names).Select(RuntimeOperations.BySymbol).OfType<RuntimeOperation>().Distinct().ToArray();
            if (operations.Length > 1) throw new InvalidDataException($"同一参照类有不同操作：{string.Join('、', operations.Select(o => o.Id))}");
        }
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
