using System.Text;
using System.Text.Json;
using Cpp2CS.Pipeline;
using Cpp2CS.Tests.Metrics;
using Mono.Cecil;

namespace Cpp2CS.Tests;

internal static class PipelineCorpusChecks
{
    public const string Command = "pipeline-corpus";
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        {
            Console.WriteLine("跳过 Pipeline 定向检查：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。");
            return 0;
        }
        var checks = new Assertions();
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "pipeline-corpus.local.output");
        var report = new RecoverySession().Run(new(
            Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a", "libil2cpp.so"),
            Path.Combine(corpus, "artifacts", "il2cppOutput", "data", "Metadata", "global-metadata.dat"), output));
        var byId = report.Methods.ToDictionary(m => m.Identity);
        using var methods = InputCorpusChecks.Json(truth, "methods.json");
        using var cases = InputCorpusChecks.Json(truth, "cases.json");
        using var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(Path.Combine(corpus, "artifacts", "ManagedStripped"));
        var metrics = new Dictionary<string, MethodMetric>();
        var options = new MetricOptions();
        foreach (var group in methods.RootElement.EnumerateArray().GroupBy(m => m.GetProperty("assembly").GetString()!))
        {
            using var reference = ModuleDefinition.ReadModule(Path.Combine(corpus, "artifacts", "ManagedStripped", group.Key), new ReaderParameters { AssemblyResolver = resolver });
            using var tested = ModuleDefinition.ReadModule(Path.Combine(output, group.Key));
            var index = tested.GetTypes().SelectMany(t => t.Methods).ToDictionary(IlMetrics.Identity);
            foreach (var row in group)
            {
                var id = row.GetProperty("id").GetString()!;
                var method = IlCompareCommand.ReferenceMethod(reference, row);
                var recovered = byId.GetValueOrDefault(id);
                var candidate = recovered?.Status == MethodStatus.Complete ? index.GetValueOrDefault(IlMetrics.Identity(method)) : null;
                metrics.Add(id, IlMetrics.Compare(method, candidate, options));
            }
        }
        var table = new StringBuilder("| 方法 | 管线状态 | IL 对照 |\n|---|---|---|\n");
        foreach (var row in cases.RootElement.EnumerateArray())
        {
            var id = row.GetProperty("mapping").GetProperty("metadata_method_id").GetString()!;
            var method = byId.GetValueOrDefault(id);
            var metric = metrics[id];
            var name = row.GetProperty("case").GetProperty("type").GetString() + "::" + row.GetProperty("case").GetProperty("method").GetString();
            var status = method?.Hole is { } hole ? $"{hole.Layer} / {hole.Reason.Code}：{hole.Reason.Message}" : method?.Status.ToString() ?? "无入口";
            table.AppendLine($"| {name} | {status} | {metric.Status}{(metric.Status == MetricStatus.Inconclusive ? " / " + metric.ReasonKind : "")} |");
            checks.True(method is not null, "用例有管线记录：" + id);
            if (method?.Status == MethodStatus.Hole) checks.True(metric.Status == MetricStatus.NotWritten, "洞不比较占位体：" + id);
        }
        var comparison = IlMetrics.Report(metrics.OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => p.Value).ToArray(), options);
        File.WriteAllText(Path.Combine(output, "comparison.local.json"), IlMetrics.Json(comparison));
        table.AppendLine($"\n管线：{report.Summary.Methods} 方法，完整 {report.Summary.Complete}，洞 {report.Summary.Holes}。");
        table.AppendLine("全部真值方法：" + string.Join("，", comparison.Summary.Statuses.Select(p => $"{p.Key}={p.Value.Count}")) + "。");
        table.AppendLine("无法判定原因：" + string.Join("，", comparison.Summary.Reasons.OrderBy(p => p.Key).Select(p => $"{p.Key}={p.Value}")) + "。");
        var complete = IlMetrics.Report(metrics.Where(p => byId.GetValueOrDefault(p.Key)?.Status == MethodStatus.Complete).Select(p => p.Value).ToArray(), options);
        table.AppendLine("完整写出方法：" + string.Join("，", complete.Summary.Statuses.Select(p => $"{p.Key}={p.Value.Count}")) + "。");
        table.AppendLine("完整写出方法无法判定原因：" + string.Join("，", complete.Summary.Reasons.OrderBy(p => p.Key).Select(p => $"{p.Key}={p.Value}")) + "。");
        table.AppendLine($"管线耗时 {report.Summary.ElapsedSeconds:F2}s，进程峰值 {report.Summary.PeakWorkingSetBytes / 1048576.0:F1} MiB。");
        File.WriteAllText(Path.Combine(output, "progress.local.md"), table.ToString());
        Console.Write(table);
        checks.True(comparison.Methods.All(m => m.Status != MetricStatus.Mismatch), "没有 IL 对照不一致");
        return checks.Finish("Pipeline 定向检查");
    }
}
