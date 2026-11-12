using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Tests.Execution;
using Mono.Cecil;

namespace Cpp2CS.Tests.Metrics;

internal static class GenericSelfCorpusChecks
{
    public const string Command = "generic-self-corpus";
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("泛型定义语料自对照：未设置 CPP2CS_CORPUS、CPP2CS_CORPUS_TRUTH，跳过。"); return 0; }
        var timer = Stopwatch.StartNew();
        using var table = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "methods.json")));
        var options = new MetricOptions();
        var metrics = new List<MethodMetric>();
        foreach (var group in table.RootElement.EnumerateArray().GroupBy(r => r.GetProperty("assembly_path").GetString()!))
        {
            var path = Path.Combine(corpus, group.Key);
            using var leftResolver = Resolver(path);
            using var rightResolver = Resolver(path);
            using var left = ModuleDefinition.ReadModule(path, new ReaderParameters { AssemblyResolver = leftResolver });
            using var right = ModuleDefinition.ReadModule(path, new ReaderParameters { AssemblyResolver = rightResolver });
            var factory = CecilModel.Factory(left, right);
            foreach (var row in group)
            {
                var method = IlCompareCommand.ReferenceMethod(left, row);
                if (!CilComparison.IsGenericEntry(method)) continue;
                metrics.Add(IlMetrics.Compare(method, IlCompareCommand.ReferenceMethod(right, row), options, factory));
                if (metrics.Count % 100 == 0) Console.WriteLine($"泛型定义语料自对照进度：{metrics.Count} 方法，{timer.Elapsed.TotalSeconds:F1}s");
            }
        }
        var report = IlMetrics.Report(metrics.ToArray(), options);
        var rounds = new[] { "ref", "value" }.ToDictionary(name => name, name =>
        {
            var instances = metrics.Select(m => m.Instances![name]).ToArray();
            return new { Applicable = instances.Count(i => i.Applicable), Match = instances.Count(i => i.Status == MetricStatus.Match),
                Mismatch = instances.Count(i => i.Status == MetricStatus.Mismatch),
                Inconclusive = instances.Count(i => i.Applicable && i.Status == MetricStatus.Inconclusive) };
        });
        var topReasons = metrics.Where(m => m.Status == MetricStatus.Inconclusive)
            .GroupBy(m => (m.ReasonKind, m.Difference)).OrderByDescending(g => g.Count())
            .ThenBy(g => g.Key.ReasonKind).ThenBy(g => g.Key.Difference, StringComparer.Ordinal).Take(10)
            .Select(g => new { Reason = g.Key.ReasonKind, Detail = g.Key.Difference, Count = g.Count() }).ToArray();
        var summary = new { report.Summary, Instances = rounds, TopReasons = topReasons };
        var output = Environment.GetEnvironmentVariable("CPP2CS_GENERIC_SELF_OUTPUT") ?? "artifacts/generic-self.local.output";
        Directory.CreateDirectory(output);
        File.WriteAllText(Path.Combine(output, "comparison.local.json"), IlMetrics.Json(report));
        File.WriteAllText(Path.Combine(output, "summary.local.json"), IlMetrics.Json(summary));
        Console.WriteLine(IlMetrics.Json(summary));
        Console.WriteLine($"泛型定义语料自对照：{metrics.Count} 方法，{timer.Elapsed.TotalSeconds:F3}s。");
        var assertions = new Assertions();
        assertions.True(metrics.Count > 0, "语料包含泛型入口");
        assertions.True(metrics.All(m => m.Status is MetricStatus.Match or MetricStatus.Inconclusive), "自对照没有不一致或没写出");
        return assertions.Finish(Command);
    }

    private static DefaultAssemblyResolver Resolver(string path)
    {
        var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(Path.GetDirectoryName(path)!);
        return resolver;
    }
}
