using System.Collections.Concurrent;
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
            Path.Combine(corpus, "artifacts", "il2cppOutput", "data", "Metadata", "global-metadata.dat"), output)
        {
            // 运行时函数的定位目前只有“符号”这一种证据；语料上由同一次构建的未去符号文件提供。
            Symbols = Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a", "libil2cpp.dbg.so"),
            Jobs = Environment.ProcessorCount,
        });
        var byId = report.Methods.ToDictionary(m => m.Identity);
        using var methods = InputCorpusChecks.Json(truth, "methods.json");
        using var cases = InputCorpusChecks.Json(truth, "cases.json");
        var metrics = new ConcurrentDictionary<string, MethodMetric>();
        var bodyless = new ConcurrentBag<string>();
        var options = new MetricOptions();
        var workers = Environment.ProcessorCount;
        var partitions = methods.RootElement.EnumerateArray().GroupBy(m => m.GetProperty("assembly").GetString()!)
            .SelectMany(group => group.Select((row, i) => (row, i)).GroupBy(x => x.i % workers)
                .Select(part => (Assembly: group.Key, Rows: part.Select(x => x.row).ToArray()))).ToArray();
        Parallel.ForEach(partitions, new ParallelOptions { MaxDegreeOfParallelism = workers }, partition =>
        {
            // Cecil 的解析缓存可变；每个分区独立加载，两侧执行世界仍由逐方法对照创建。
            using var resolver = new DefaultAssemblyResolver();
            resolver.AddSearchDirectory(Path.Combine(corpus, "artifacts", "ManagedStripped"));
            using var reference = ModuleDefinition.ReadModule(Path.Combine(corpus, "artifacts", "ManagedStripped", partition.Assembly), new ReaderParameters { AssemblyResolver = resolver });
            // 待测模块的外部引用在输出目录里解析；否则会落到宿主运行时的同名程序集，比较的就不是被测的输出。
            using var testedResolver = new DefaultAssemblyResolver();
            testedResolver.AddSearchDirectory(output);
            using var tested = ModuleDefinition.ReadModule(Path.Combine(output, partition.Assembly), new ReaderParameters { AssemblyResolver = testedResolver });
            var index = tested.GetTypes().SelectMany(t => t.Methods).ToDictionary(IlMetrics.Identity);
            var modelFactory = Execution.CecilModel.Factory(reference, tested);
            foreach (var row in partition.Rows)
            {
                var id = row.GetProperty("id").GetString()!;
                var method = IlCompareCommand.ReferenceMethod(reference, row);
                var recovered = byId.GetValueOrDefault(id);
                // 管线按元数据判断“声明没有方法体”；与参考程序集核对，判错的不得悄悄移出分母。
                if (recovered is not null && (recovered.Status == MethodStatus.NoBody) == method.HasBody) bodyless.Add(id);
                var candidate = recovered?.Status == MethodStatus.Complete ? index.GetValueOrDefault(IlMetrics.Identity(method)) : null;
                if (!metrics.TryAdd(id, IlMetrics.Compare(method, candidate, options, modelFactory)))
                    throw new InvalidDataException("真值方法身份重复。");
            }
        });
        checks.True(bodyless.IsEmpty, "声明没有方法体的判断与参考程序集一致：" + string.Join("、", bodyless.Order(StringComparer.Ordinal).Take(5)));
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
        table.AppendLine($"\n管线：{report.Summary.Methods} 方法，完整 {report.Summary.Complete}，洞 {report.Summary.Holes}，声明没有方法体 {report.Summary.NoBody}。");
        table.AppendLine("全部真值方法：" + string.Join("，", comparison.Summary.Statuses.Select(p => $"{p.Key}={p.Value.Count}")) + "。");
        table.AppendLine("无法判定原因：" + string.Join("，", comparison.Summary.Reasons.OrderBy(p => p.Key).Select(p => $"{p.Key}={p.Value}")) + "。");
        var complete = IlMetrics.Report(metrics.Where(p => byId.GetValueOrDefault(p.Key)?.Status == MethodStatus.Complete).Select(p => p.Value).ToArray(), options);
        table.AppendLine("完整写出方法：" + string.Join("，", complete.Summary.Statuses.Select(p => $"{p.Key}={p.Value.Count}")) + "。");
        table.AppendLine("完整写出方法无法判定原因：" + string.Join("，", complete.Summary.Reasons.OrderBy(p => p.Key).Select(p => $"{p.Key}={p.Value}")) + "。");
        table.AppendLine($"管线耗时 {report.Summary.ElapsedSeconds:F2}s，进程峰值 {report.Summary.PeakWorkingSetBytes / 1048576.0:F1} MiB。");
        File.WriteAllText(Path.Combine(output, "progress.local.md"), table.ToString());
        Console.Write(table);
        Console.WriteLine("layer_seconds=" + JsonSerializer.Serialize(report.Summary.LayerSeconds));
        Console.WriteLine($"no_return_seconds={report.Summary.LayerSeconds.GetValueOrDefault("不返回分析"):F3}");
        checks.True(comparison.Methods.All(m => m.Status != MetricStatus.Mismatch), "没有 IL 对照不一致");
        return checks.Finish("Pipeline 定向检查");
    }
}
