using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.Json.Serialization;
using Cpp2CS.Tests.Execution;
using Mono.Cecil;

namespace Cpp2CS.Tests.Metrics;

public enum MetricStatus { NotWritten, Match, Mismatch, Inconclusive }
public sealed record MetricOptions(int Cases = 32, int StepLimit = 10000, int FirstSeed = 0);
public sealed record MethodMetric(string Identity, MetricStatus Status, ComparisonReason ReasonKind,
    string? Difference, int? Seed, int CompletedCases, int NaNSkippedCases, CoverageResult? Coverage)
{
    public CoverageResult? AttemptedCoverage { get; init; }
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
    public IReadOnlyDictionary<string, InstanceMetric>? Instances { get; init; }
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
    public Cpp2CS.Managed.GenericWitnessCoverage? WitnessCoverage { get; init; }
}
public sealed record InstanceMetric(bool Applicable, MetricStatus Status, ComparisonReason ReasonKind,
    string? Difference, int? Seed, int CompletedCases, int NaNSkippedCases, CoverageResult? Coverage);
public sealed record CountRatio(int Count, double Ratio);
public sealed record MetricSummary(Dictionary<string, CountRatio> Statuses, Dictionary<string, int> Reasons,
    Dictionary<string, int> Coverage, int NaNAffectedMethods);
public sealed record MetricReport(int FormatVersion, MetricOptions Options, MethodMetric[] Methods, MetricSummary Summary);

public static class IlMetrics
{
    // 类型使用元数据作用域和泛型位置；不使用参数名、标记或近似字符串匹配。
    internal static string TypeKey(TypeReference t, ModuleDefinition module) => t switch
    {
        GenericParameter p => (p.Type == GenericParameterType.Method ? "!!" : "!") + p.Position,
        GenericInstanceType g => TypeKey(g.ElementType, module) + "<" + string.Join(",", g.GenericArguments.Select(a => TypeKey(a, module))) + ">",
        ArrayType a => TypeKey(a.ElementType, module) + (a.IsVector ? "[]" : "[" + string.Join(",", a.Dimensions) + "]"),
        FunctionPointerType f => $"method {f.CallingConvention} {f.HasThis} {f.ExplicitThis} " + TypeKey(f.ReturnType, module)
            + "(" + string.Join(",", f.Parameters.Select(p => TypeKey(p.ParameterType, module))) + ")",
        PinnedType p => TypeKey(p.ElementType, module) + " pinned",
        SentinelType s => TypeKey(s.ElementType, module) + " sentinel",
        ByReferenceType b => TypeKey(b.ElementType, module) + "&",
        PointerType p => TypeKey(p.ElementType, module) + "*",
        OptionalModifierType m => TypeKey(m.ElementType, module) + " modopt(" + TypeKey(m.ModifierType, module) + ")",
        RequiredModifierType m => TypeKey(m.ElementType, module) + " modreq(" + TypeKey(m.ModifierType, module) + ")",
        _ => (t.Scope == module ? "input" : t.Scope?.ToString()) + ":" + t.FullName
    };
    public static string Identity(MethodDefinition m) => TypeKey(m.DeclaringType, m.Module) + "::" + m.Name + "`" + m.GenericParameters.Count
        + "(" + string.Join(",", m.Parameters.Select(p => TypeKey(p.ParameterType, m.Module))) + ")->" + TypeKey(m.ReturnType, m.Module)
        + $"|{m.CallingConvention}|{m.HasThis}|{m.ExplicitThis}";

    public static MethodMetric Compare(MethodDefinition reference, MethodDefinition? tested, MetricOptions options) => Compare(reference, tested, options, null);
    internal static MethodMetric Compare(MethodDefinition reference, MethodDefinition? tested, MetricOptions options, Func<CecilModel>? modelFactory,
        Cpp2CS.Managed.GenericWitnessCoverage? witnessCoverage = null)
    {
        var hasBody = reference.HasBody && reference.Body.Instructions.Count > 0;
        if (!hasBody)
            return new(Identity(reference), MetricStatus.Inconclusive, ComparisonReason.MissingBody, "参考方法没有 CIL 方法体", null, 0, 0, null)
            { Instances = UnavailableInstances(reference, MetricStatus.Inconclusive, "参考方法没有 CIL 方法体") };
        if (tested is null || !tested.HasBody || tested.Body.Instructions.Count == 0)
            return new(Identity(reference), MetricStatus.NotWritten, ComparisonReason.MissingBody, null, null, 0, 0, null)
            { Instances = UnavailableInstances(reference, MetricStatus.NotWritten, null) };
        var result = CilComparison.Compare(reference, tested, options.Cases, options.FirstSeed, options.StepLimit, modelFactory, witnessCoverage);
        return new(Identity(reference), Status(result.Status), result.ReasonKind, result.Reason, result.Seed, result.CompletedCases, result.NaNSkippedCases, result.Coverage)
        {
            WitnessCoverage = witnessCoverage,
            AttemptedCoverage = result.AttemptedCoverage,
            Instances = result.Instances?.ToDictionary(p => p.Key, p => new InstanceMetric(p.Value.Applicable,
                Status(p.Value.Result.Status), p.Value.Result.ReasonKind, p.Value.Result.Reason, p.Value.Result.Seed,
                p.Value.Result.CompletedCases, p.Value.Result.NaNSkippedCases, p.Value.Result.Coverage))
        };
    }
    private static MetricStatus Status(CilComparisonStatus status) => status switch
    {
        CilComparisonStatus.Match => MetricStatus.Match,
        CilComparisonStatus.Mismatch => MetricStatus.Mismatch,
        _ => MetricStatus.Inconclusive
    };
    private static IReadOnlyDictionary<string, InstanceMetric>? UnavailableInstances(MethodDefinition method, MetricStatus status, string? detail) =>
        !CilComparison.IsGenericEntry(method) ? null : new[] { ("ref", false), ("value", true) }.ToDictionary(i => i.Item1,
            i => new InstanceMetric(CilComparison.Applicable(method, i.Item2), status, ComparisonReason.MissingBody, detail, null, 0, 0, null));
    public static MetricReport Compare(ModuleDefinition reference, ModuleDefinition tested, IEnumerable<MethodDefinition> methods, MetricOptions options)
    {
        var index = tested.GetTypes().SelectMany(t => t.Methods).ToDictionary(Identity, StringComparer.Ordinal);
        return Report(methods.Select(m => Compare(m, index.GetValueOrDefault(Identity(m)), options)).ToArray(), options);
    }
    public static MetricReport Report(MethodMetric[] methods, MetricOptions options)
    {
        var matches = methods.Where(m => m.Status == MetricStatus.Match).ToArray();
        return new(1, options, methods, new(
            Enum.GetValues<MetricStatus>().ToDictionary(s => s.ToString(), s => new CountRatio(methods.Count(m => m.Status == s), methods.Length == 0 ? 0 : (double)methods.Count(m => m.Status == s) / methods.Length)),
            methods.Where(m => m.Status == MetricStatus.Inconclusive).GroupBy(m => m.ReasonKind.ToString()).ToDictionary(g => g.Key, g => g.Count()),
            new() { ["Complete"] = matches.Count(m => m.Coverage?.Complete == true),
                ["MissingBranch"] = matches.Count(m => m.Coverage!.Branches.Any(b => b.Directions.Any(d => !d))),
                ["MissingInstructionsOnly"] = matches.Count(m => m.Coverage is { Complete: false } c && c.Branches.All(b => b.Directions.All(d => d))) },
            methods.Count(m => m.NaNSkippedCases > 0)));
    }
    public static string Json<T>(T report)
    {
        var options = new JsonSerializerOptions { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower };
        options.Converters.Add(new JsonStringEnumConverter());
        var node = JsonSerializer.SerializeToNode(report, options)!;
        JsonNode? Sort(JsonNode? value) => value switch
        {
            JsonObject obj => new JsonObject(obj.OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => KeyValuePair.Create(p.Key, Sort(p.Value)))),
            JsonArray array => new JsonArray(array.Select(Sort).ToArray()),
            _ => value?.DeepClone()
        };
        return Sort(node)!.ToJsonString(options) + "\n";
    }
}

internal static class IlCompareCommand
{
    public const string Command = "il-compare";
    public static int Run()
    {
        var input = Environment.GetEnvironmentVariable("CPP2CS_IL_COMPARE_REQUEST");
        if (input is null) { Console.WriteLine("il-compare：未提供请求，跳过；使用 Metrics/il-compare 包装命令。"); return 0; }
        var args = JsonSerializer.Deserialize<string[]>(input)!;
        if (args.Length is < 4 or > 7) throw new ArgumentException("reference tested methods output [cases] [steps] [first-seed]");
        var options = new MetricOptions(args.Length > 4 ? int.Parse(args[4]) : 32, args.Length > 5 ? int.Parse(args[5]) : 10000, args.Length > 6 ? int.Parse(args[6]) : 0);
        using var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(Path.GetDirectoryName(Path.GetFullPath(args[0]))!);
        resolver.AddSearchDirectory(Path.GetDirectoryName(Path.GetFullPath(args[1]))!);
        resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(object).Assembly.Location)!);
        using var reference = ModuleDefinition.ReadModule(args[0], new ReaderParameters { AssemblyResolver = resolver });
        using var tested = ModuleDefinition.ReadModule(args[1], new ReaderParameters { AssemblyResolver = resolver });
        using var table = JsonDocument.Parse(File.ReadAllText(args[2]));
        var methods = table.RootElement.EnumerateArray().Where(e => e.GetProperty("assembly").GetString() == Path.GetFileName(args[0]))
            .Select(e => ReferenceMethod(reference, e)).ToArray();
        if (methods.Length == 0) throw new InvalidDataException("方法表没有参考程序集的方法");
        var report = IlMetrics.Compare(reference, tested, methods, options);
        File.WriteAllText(args[3], IlMetrics.Json(report));
        Console.WriteLine(IlMetrics.Json(report.Summary));
        return report.Methods.Any(m => m.Status == MetricStatus.Mismatch) ? 1 : 0;
    }
    internal static MethodDefinition ReferenceMethod(ModuleDefinition module, JsonElement row)
    {
        var method = (MethodDefinition)module.LookupToken(Convert.ToInt32(row.GetProperty("token").GetString()![2..], 16));
        if (method.FullName != row.GetProperty("signature").GetString() || method.GenericParameters.Count != row.GetProperty("generic_arity").GetInt32()
            || module.Mvid.ToString() != row.GetProperty("module_mvid").GetString())
            throw new InvalidDataException("方法表与参考程序集不匹配");
        return method;
    }
}
