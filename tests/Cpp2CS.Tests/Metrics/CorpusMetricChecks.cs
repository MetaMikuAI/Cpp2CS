using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Tests.Execution;
using Mono.Cecil;

namespace Cpp2CS.Tests.Metrics;

internal sealed record MutationObservation(string Method, MutationKind Kind, int Offset, MetricStatus Status,
    ComparisonReason Reason, string? Detail, int? Seed, bool Reached, string Classification);
internal sealed record SensitivityCount(int Generated, int Detected, double Rate, int Reached, int ReachedDetected,
    double ReachedRate, int NotExecuted, int Equivalent, int Other, int Inapplicable);
internal static class CorpusMetricChecks
{
    public const string Command = "il-metrics-corpus";
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("IL 指标定向检查：未设置 CPP2CS_CORPUS、CPP2CS_CORPUS_TRUTH，跳过。"); return 0; }
        using var table = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "methods.json")));
        using var cases = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "cases.json")));
        var caseAssemblies = cases.RootElement.EnumerateArray().Select(c => c.GetProperty("method").GetProperty("assembly").GetString()).ToHashSet();
        var all = table.RootElement.EnumerateArray().ToArray();
        var libraries = all.Where(r => !caseAssemblies.Contains(r.GetProperty("assembly").GetString())).ToArray();
        // 参考库按方法表的次序等距抽取。日常只抽两百个；量指标时用 CPP2CS_IL_METRICS_LIBRARY 指定（基线是两千个）。
        var sample = int.TryParse(Environment.GetEnvironmentVariable("CPP2CS_IL_METRICS_LIBRARY"), out var requested) && requested > 0 ? requested : 200;
        if (libraries.Length < sample) throw new InvalidDataException("参考库的方法数少于要抽取的个数");
        var selected = all.Where(r => caseAssemblies.Contains(r.GetProperty("assembly").GetString()))
            .Concat(Enumerable.Range(0, sample).Select(n => libraries[(int)((long)n * libraries.Length / sample)])).ToArray();
        var options = new MetricOptions(32, 10000);
        var assertions = new Assertions();
        var metrics = new List<MethodMetric>();
        var observations = new List<MutationObservation>();
        var timer = Stopwatch.StartNew();
        double comparisonSeconds = 0, mutationSeconds = 0;
        foreach (var group in selected.GroupBy(r => r.GetProperty("assembly_path").GetString()!))
        {
            var path = Path.Combine(corpus, group.Key);
            using var leftResolver = Resolver(path);
            using var rightResolver = Resolver(path);
            using var left = ModuleDefinition.ReadModule(path, new ReaderParameters { AssemblyResolver = leftResolver });
            using var right = ModuleDefinition.ReadModule(path, new ReaderParameters { AssemblyResolver = rightResolver });
            foreach (var row in group)
            {
                var l = IlCompareCommand.ReferenceMethod(left, row);
                var r = IlCompareCommand.ReferenceMethod(right, row);
                var start = timer.Elapsed.TotalSeconds;
                var result = IlMetrics.Compare(l, r, options);
                comparisonSeconds += timer.Elapsed.TotalSeconds - start;
                metrics.Add(result);
                assertions.True(result.Status is MetricStatus.Match or MetricStatus.Inconclusive, "真值自对照无差异：" + result.Identity);
                start = timer.Elapsed.TotalSeconds;
                foreach (var mutation in Mutations.Generate(r).ToArray())
                {
                    var original = r.Body;
                    r.Body = Mutations.Changed(r, mutation);
                    var changed = IlMetrics.Compare(l, r, options);
                    r.Body = original;
                    var reached = changed.AttemptedCoverage is { Visited: > 0 } coverage && !coverage.Unvisited.Contains(mutation.Offset);
                    var classification = changed.Status == MetricStatus.Mismatch ? "Detected"
                        : changed.Status == MetricStatus.Match && !reached ? "NotExecuted" : "Other";
                    observations.Add(new(result.Identity, mutation.Kind, mutation.Offset, changed.Status, changed.ReasonKind,
                        changed.Difference, changed.Seed, reached, classification));
                    if (classification == "NotExecuted") assertions.True(changed.Coverage!.Unvisited.Contains(mutation.Offset), "未执行改动与覆盖位置一致");
                }
                mutationSeconds += timer.Elapsed.TotalSeconds - start;
                if (metrics.Count % 100 == 0) Console.WriteLine($"IL 指标进度：{metrics.Count}/{selected.Length} 方法，{observations.Count} 改动，{timer.Elapsed.TotalSeconds:F1}s");
            }
        }
        var report = IlMetrics.Report(metrics.ToArray(), options);
        var sensitivity = Enum.GetValues<MutationKind>().ToDictionary(k => k.ToString(), k =>
        {
            var rows = observations.Where(o => o.Kind == k).ToArray();
            var found = rows.Count(o => o.Status == MetricStatus.Mismatch);
            var reached = rows.Count(o => o.Reached);
            var reachedFound = rows.Count(o => o.Reached && o.Status == MetricStatus.Mismatch);
            return new SensitivityCount(rows.Length, found, rows.Length == 0 ? 0 : (double)found / rows.Length,
                reached, reachedFound, reached == 0 ? 0 : (double)reachedFound / reached,
                rows.Count(o => o.Classification == "NotExecuted"), 0, rows.Count(o => o.Classification == "Other"), selected.Length - rows.Length);
        });
        // 校准中全候选发现率约 43%，最低类别约 19%；按五个百分点向下留出余量。
        // 到达集合包含未完成用例，不排除解释器拒绝的改动来抬高比率。
        var totalReached = sensitivity.Values.Sum(v => v.Reached);
        var totalDetected = sensitivity.Values.Sum(v => v.ReachedDetected);
        assertions.True(totalReached > 0 && (double)totalDetected / totalReached >= 0.40, "已到达改动的总体发现率至少 40%");
        foreach (var (kind, count) in sensitivity)
            assertions.True(count.Reached > 0 && count.ReachedRate >= 0.15, $"{kind} 已到达改动的发现率至少 15%");
        var output = Environment.GetEnvironmentVariable("CPP2CS_IL_METRICS_OUTPUT") ?? "artifacts/il-metrics.local.output";
        Directory.CreateDirectory(output);
        File.WriteAllText(Path.Combine(output, "comparison.local.json"), IlMetrics.Json(report));
        File.WriteAllText(Path.Combine(output, "sensitivity.local.json"), IlMetrics.Json(new { Options = options, Summary = sensitivity, Observations = observations }));
        Console.WriteLine(IlMetrics.Json(report.Summary));
        Console.WriteLine(IlMetrics.Json(sensitivity));
        Console.WriteLine($"IL 指标用时：自对照 {comparisonSeconds:F3}s，变异 {mutationSeconds:F3}s，总计 {timer.Elapsed.TotalSeconds:F3}s；{selected.Length} 方法。");
        return assertions.Finish("IL 指标定向检查");
    }
    private static DefaultAssemblyResolver Resolver(string path)
    {
        var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(Path.GetDirectoryName(path)!);
        resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(object).Assembly.Location)!);
        return resolver;
    }
}
