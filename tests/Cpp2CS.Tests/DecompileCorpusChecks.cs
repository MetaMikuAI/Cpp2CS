using System.Collections.Concurrent;
using System.Text;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Mono.Cecil;

namespace Cpp2CS.Tests;

internal static class DecompileCorpusChecks
{
    public const string Command = "decompile-corpus";
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        {
            Console.WriteLine("跳过 C# 导出定向检查：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。");
            return 0;
        }
        var checks = new Assertions();
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "decompile-corpus.local.output");
        var managed = Path.Combine(corpus, "artifacts", "ManagedStripped");
        Directory.CreateDirectory(output);
        using var cases = InputCorpusChecks.Json(truth, "cases.json");
        var caseRows = cases.RootElement.EnumerateArray().ToArray();
        var texts = new StringBuilder();
        var statistics = new StringBuilder();
        var failures = new List<SourceTypeFailure>();
        var total = 0;
        var successful = 0;
        var caseCount = 0;
        var allTypes = 0;
        var successfulTypes = 0;
        foreach (var path in Directory.GetFiles(managed, "*.dll").Order(StringComparer.Ordinal))
        {
            using var module = ModuleDefinition.ReadModule(path);
            var expected = module.Types.Count(t => t.Name != "<Module>");
            var failed = new ConcurrentBag<SourceFailure>();
            var sources = Decompilation.Decompile(path, managed, _ => true, false, failure: failed.Add);
            var name = Path.GetFileName(path);
            foreach (var source in sources)
                File.WriteAllText(Path.Combine(output, name + "_" + Safe(source.TypeName!) + ".cs"), source.Source);
            var distinct = failed.DistinctBy(f => (f.Namespace, f.TypeName)).ToArray();
            failures.AddRange(distinct.Select(f => new SourceTypeFailure(name, f.TypeName, f.Reason)));
            var failedNames = distinct.Select(f => f.TypeName).ToHashSet();
            foreach (var type in module.GetTypes().Where(t => t.Name != "<Module>"))
            {
                allTypes++;
                var top = type;
                while (top.DeclaringType is not null) top = top.DeclaringType;
                if (!failedNames.Contains(top.FullName)) successfulTypes++;
            }
            total += expected;
            successful += expected - distinct.Length;
            statistics.AppendLine($"{name}: {expected - distinct.Length}/{expected}");
            Console.WriteLine($"C# {name}: {expected - distinct.Length}/{expected}");
            foreach (var row in caseRows.Where(r => r.GetProperty("method").GetProperty("assembly").GetString() == name))
            {
                var method = row.GetProperty("method");
                var token = Convert.ToInt32(method.GetProperty("token").GetString()![2..], 16);
                var definition = (MethodDefinition)module.LookupToken(token);
                var top = definition.DeclaringType;
                while (top.DeclaringType is not null) top = top.DeclaringType;
                var source = sources.SingleOrDefault(s => s.TypeName == top.FullName);
                var declarations = source is null ? [] : CSharpSyntaxTree.ParseText(source.Source).GetRoot().DescendantNodes()
                    .OfType<MethodDeclarationSyntax>().Where(m => m.Identifier.ValueText == definition.Name
                        && m.ParameterList.Parameters.Count == definition.Parameters.Count).ToArray();
                checks.True(!distinct.Any(f => f.TypeName == top.FullName) && declarations.Length == 1,
                    "用例方法导出成功：" + definition.FullName);
                if (declarations.Length != 1) continue;
                caseCount++;
                texts.AppendLine($"// {method.GetProperty("id").GetString()} {definition.FullName}");
                texts.AppendLine(declarations[0].ToFullString());
            }
        }
        statistics.AppendLine($"顶层类型：{successful}/{total} ({100.0 * successful / total:F2}%)；用例方法：{caseCount}/{caseRows.Length}。");
        statistics.AppendLine($"含嵌套类型：{successfulTypes}/{allTypes} ({100.0 * successfulTypes / allTypes:F2}%)。");
        foreach (var group in failures.GroupBy(f => f.Reason).OrderByDescending(g => g.Count()))
            statistics.AppendLine($"失败 {group.Count()}：{group.Key}");
        File.WriteAllText(Path.Combine(output, "cases.local.cs.txt"), texts.ToString());
        File.WriteAllText(Path.Combine(output, "failures.local.json"), RecoveryReport.Json(failures));
        checks.True(caseRows.Length == 42 && caseCount == 42, "42 个用例方法全部导出");
        var pipeline = Path.Combine(output, "pipeline.local.output");
        var report = new RecoverySession().Run(new(
            Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a", "libil2cpp.so"),
            Path.Combine(corpus, "artifacts", "il2cppOutput", "data", "Metadata", "global-metadata.dat"), pipeline) { Source = true });
        checks.True(report.Source is { Files: > 0 }, "管线 C# 导出完成");
        statistics.AppendLine($"管线：{report.Summary.Methods} 方法，完整 {report.Summary.Complete}，洞 {report.Summary.Holes}；C# {report.Source!.Files} 文件，失败 {report.Source.Types.Length} 类型/{report.Source.Methods.Length} 方法。");
        File.WriteAllText(Path.Combine(output, "summary.local.txt"), statistics.ToString());
        Console.Write(statistics);
        return checks.Finish("C# 导出定向检查");
    }
    private static string Safe(string name) => new(name.Select(c => Path.GetInvalidFileNameChars().Contains(c) ? '_' : c).ToArray());
}
