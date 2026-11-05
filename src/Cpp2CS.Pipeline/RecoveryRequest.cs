
namespace Cpp2CS.Pipeline;

/// <summary>一次恢复的显式输入、范围和输出策略。</summary>
public sealed record RecoveryRequest(string Binary, string Metadata, string Output)
{
    public Cpp2CS.Options.RecoveryOptions Options { get; init; } = new();
    public string Profile { get; init; } = "core";
    public bool All { get; init; }
    public string[] Namespaces { get; init; } = [];
    public string[]? Assemblies { get; init; }
    public string? Methods { get; init; }
    /// <summary>顶层类型全名清单（每行一个，取制表符前的第一列）；选择这些类型及其嵌套类型的全部方法。</summary>
    public string? Types { get; init; }
    public int Limit { get; init; } = int.MaxValue;
    public int Jobs { get; init; } = 1;
    public bool NoSource { get; init; }
    /// <summary>只导出桩：不恢复方法体，每个方法都是占位体。类型、成员和签名与正常导出相同。</summary>
    public bool StubsOnly { get; init; }
    public string SourceLayout { get; init; } = "flat";

    public bool HasScope => (All ? 1 : 0) + (Namespaces.Length > 0 ? 1 : 0)
        + (Assemblies is { Length: > 0 } ? 1 : 0) + (!string.IsNullOrWhiteSpace(Methods) ? 1 : 0) + (!string.IsNullOrWhiteSpace(Types) ? 1 : 0) == 1;

    public void Validate()
    {
        if (Profile != "core") throw new ArgumentException("--profile 只支持 core");
        if (!HasScope) throw new ArgumentException("必须且只能指定一种恢复范围");
        if (Jobs < 1) throw new ArgumentException("--jobs 必须大于零");
        if (Limit < 1) throw new ArgumentException("--limit 必须大于零");
        if (SourceLayout is not ("flat" or "project")) throw new ArgumentException("--source-layout 必须是 flat 或 project");
    }

    public static RecoveryRequest Parse(string binary, string metadata, string output, string[] options)
    {
        var request = new RecoveryRequest(binary, metadata, output) { Options = RecoveryEnvironment.Read() };
        var scopes = 0;
        for (var i = 0; i < options.Length; i++)
        {
            var option = options[i];
            if (option == "--all") { request = request with { All = true }; scopes++; continue; }
            if (option == "--no-source") { request = request with { NoSource = true }; continue; }
            if (option == "--stubs-only") { request = request with { StubsOnly = true }; continue; }
            if (++i == options.Length) throw new ArgumentException($"{option} 缺少参数");
            var value = options[i];
            if (option is "--namespaces" or "--assemblies" or "--methods" or "--types") scopes++;
            request = option switch
            {
                "--profile" => request with { Profile = value },
                "--fact-cache-file" => request with { Options = request.Options with { FactCacheFile = Path.GetFullPath(value) } },
                "--namespaces" => request with { Namespaces = Split(value) },
                "--assemblies" => request with { Assemblies = Split(value) },
                "--methods" => request with { Methods = value },
                "--types" => request with { Types = value },
                "--limit" => request with { Limit = int.Parse(value) },
                "--jobs" => request with { Jobs = int.Parse(value) },
                "--source-layout" => request with { SourceLayout = value },
                _ => throw new ArgumentException($"未知参数 {option}"),
            };
        }
        if (scopes != 1) return request with { All = false, Namespaces = [], Assemblies = null, Methods = null, Types = null };
        return request;
    }

    /// <summary>类型清单中的顶层类型全名。</summary>
    public HashSet<string>? TypeNames() => Types is null ? null
        : File.ReadLines(Types).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t')[0].Trim()).ToHashSet(StringComparer.Ordinal);

    private static string[] Split(string value) => value.Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
}

/// <summary>写出统计不代表编译或执行验证；报告保留各阶段失败。</summary>
public sealed record RecoveryRunResult(string Output, string Report, int SelectedMethods, int EmittedMethods, int EmitFailures, int PartialMethods);
