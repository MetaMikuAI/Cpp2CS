using System.Text.Encodings.Web;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;

namespace Cpp2CS.Cli;

internal static class Program
{
    private static readonly JsonSerializerOptions Json = new()
    {
        WriteIndented = true,
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        return args switch
        {
            ["facts", var binary, var metadata, var output] => Facts(binary, metadata, output),
            ["refs", var binary, var metadata, var address] => Refs(binary, metadata, Convert.ToUInt64(address, 16)),
            ["layout", var binary, var metadata, var type] => Layout(binary, metadata, type),
            ["ssa", var binary, var metadata, .. var addresses] when addresses.Length > 0 => Ssa(binary, metadata, addresses.Where(a => a != "--idioms").Select(a => Convert.ToUInt64(a, 16)).ToArray(), addresses.Contains("--idioms")),
            ["idioms", var binary, var metadata, var output, .. var options] => Idioms(binary, metadata, output, options),
            ["recover", var binary, var metadata, var output, .. var options] => RecoverCommand.Run(binary, metadata, output, options),
            ["source-project", var assembly, var output] => SourceProject(assembly, output),
            ["source-project", var assembly, var output, "--profile", "full"] => SourceProject(assembly, output, full: true),
            _ => Usage(),
        };
    }

    private static int Usage()
    {
        Console.Error.WriteLine("""
            用法: cpp2cs facts  <libil2cpp.so> <global-metadata.dat> <输出目录>   建立基础事实，写出 summary.json 与 *.tsv
                  cpp2cs refs   <libil2cpp.so> <global-metadata.dat> <十六进制地址>  打印所在函数的所有者与引用
                  cpp2cs layout <libil2cpp.so> <global-metadata.dat> <类型全名>      打印类型（含泛型实例）的字段布局
                  cpp2cs ssa    <libil2cpp.so> <global-metadata.dat> <十六进制入口>... [--idioms]
                                                                      打印函数的寄存器 SSA（--idioms：L2 归一之后）
                  cpp2cs idioms <libil2cpp.so> <global-metadata.dat> <输出目录> [--owner 前缀] [--limit N]
                                                                      对托管函数做 L2 模板普查，写出 idioms.txt 与 idiom-residuals.tsv
                  cpp2cs recover <libil2cpp.so> <global-metadata.dat> <输出目录> [--all | --assemblies A.dll,B.dll | --namespaces A,B] [--no-source] [--limit N] [--jobs N] [--methods 清单] [--verified-accessors 证据.tsv] [--source-layout flat|project]
                                                                      恢复范围必须显式指定，写出 CIL 与 C#；
                                                                      --methods：从外部方法清单选择目标，候选访问器另作依赖；
                                                                      --verified-accessors：使用 execute 生成的证据认回内联访问器。
                                                                      --source-layout project：按程序集/命名空间/类型导出，含范围内全部类型声明与 csproj。
                                                                      --jobs N：方法恢复的最大并行度，默认 1；程序集写出按顺序执行。
                                                                      --profile core|full：核心链路或完整流程，默认 full。
                                                                      --fact-cache-file 文件：显式固定事实快照，输入变化仍会失效；用于重构前后对比。
                  cpp2cs source-project <程序集.dll> <输出目录> [--profile full]
                                                                      将已有程序集按项目目录导出 C#；full 启用完整源码变换，依赖从程序集所在目录解析。
            """);
        return 2;
    }

    private static int SourceProject(string assembly, string output, bool full = false)
    {
        var path = Path.GetFullPath(assembly);
        var count = Output.SourceProject.Write(path, Path.GetDirectoryName(path)!, output, _ => true,
            full ? Cpp2CS.Extensions.Decompile.ReadabilityTransforms.Instance : null);
        Console.WriteLine($"C#：{count} 个类型文件，{Path.GetFullPath(output)}");
        return 0;
    }

    /// <summary>打印一个函数的边界、所有者与引用普查结果（调试用）。</summary>
    private static int Refs(string binary, string metadata, ulong address)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var index = facts.Code.IndexOf(address);
        if (index < 0) { Console.Error.WriteLine($"0x{address:x} 不在任何函数内"); return 1; }
        var function = facts.Code.Functions[index];
        Console.WriteLine($"函数 0x{function.Start:x}..0x{function.End:x} {function.Region}/{function.Evidence} {facts.Scan.ShapeOf(index)}");
        foreach (var e in facts.EntriesAt(function.Start)) Console.WriteLine($"  所有者 {e}");
        foreach (var r in facts.Scan.Of(index))
        {
            var note = facts.Usages.At(r.Target)?.Usage.ToString() ?? facts.Helpers.At(r.Target)?.ToString()
                ?? string.Join(" | ", facts.EntriesAt(r.Target).Select(e => e.ToString())) ?? "";
            Console.WriteLine($"  0x{r.Site:x} {r.Kind,-8} 0x{r.Target:x} {(r.Size > 0 ? $"[{r.Size}]" : "")} {facts.Model.Image.SectionAt(r.Target)?.Name} {note} {(facts.Model.UsageAt(r.Target) is { } u ? "token:" + u : "")}");
        }
        return 0;
    }

    /// <summary>打印函数入口的寄存器 SSA（调试用）；idioms 为真时打印 L2 归一之后的形式与残余。</summary>
    private static int Ssa(string binary, string metadata, ulong[] entries, bool idioms)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var lifter = new Cpp2CS.Machine.Lifting.FunctionLifter(facts);
        var rewriter = new Cpp2CS.Idioms.IdiomRewriter(facts);
        foreach (var entry in entries)
        {
            Console.WriteLine($"== 0x{entry:x} {string.Join(" | ", facts.EntriesAt(entry).Select(e => e.ToString()))}");
            var lifted = lifter.Lift(entry);
            foreach (var error in lifted.Errors) Console.WriteLine($"  ! {error}");
            if (idioms && lifted.Succeeded)
            {
                var result = rewriter.Run(lifted.Function);
                Console.WriteLine($"  模板: {string.Join(", ", result.Hits.Select(p => $"{p.Key}×{p.Value}"))}");
                foreach (var error in result.Errors) Console.WriteLine($"  ! {error}");
                foreach (var residual in result.Residuals) Console.WriteLine($"  残余 0x{residual.Address:x} {residual.Category}: {residual.Detail}");
                foreach (var instance in result.Instances)
                    Console.WriteLine($"  实例 {instance.Template} 0x{instance.Head:x} {System.Text.Json.JsonSerializer.Serialize(instance.Inputs)}");
                foreach (var (block, define) in lifted.Function.Dead) Console.WriteLine($"  删去 B{block.Index}@0x{block.Start:x} 0x{define.Address:x}: {define}");
            }
            Console.Write(lifted.Function);
        }
        return 0;
    }

    /// <summary>L2 模板普查。选项：--owner 只取托管所有者全名以该前缀开头的函数；--limit 只取前 N 个。</summary>
    private static int Idioms(string binary, string metadata, string output, string[] options)
    {
        string? prefix = null;
        var limit = int.MaxValue;
        for (var i = 0; i + 1 < options.Length; i += 2)
        {
            if (options[i] == "--owner") prefix = options[i + 1];
            else if (options[i] == "--limit") limit = int.Parse(options[i + 1]);
        }
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        var functions = facts.Code.Functions.Where(f => f.Region == CodeRegion.Managed)
            .Where(f => prefix is null || facts.EntriesAt(f.Start).Any(e => e.Method is not null && e.Method.ToString().StartsWith(prefix, StringComparison.Ordinal)))
            .Take(limit).ToArray();
        Console.Error.WriteLine($"普查 {functions.Length} 个托管函数");
        var census = Cpp2CS.Idioms.IdiomCensus.Run(facts, functions, Console.Error.WriteLine);
        Directory.CreateDirectory(output);
        var report = IdiomReport.Write(facts, census, output);
        Console.Write(report);
        return 0;
    }

    /// <summary>按全名查找类型（非泛型定义按 FullName，泛型实例按运行时类型的显示名）并打印布局。</summary>
    private static int Layout(string binary, string metadata, string name)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var matches = facts.Model.Types.Where(t => t.FullName == name && t.GenericParameters.Count == 0).Select(t => new Model.DefinitionRef(t, []))
            .Concat(facts.Model.RuntimeTypes.OfType<Model.DefinitionRef>().Where(d => d.Arguments.Count > 0 && d.ToString() == name)).Distinct().ToArray();
        if (matches.Length == 0) { Console.Error.WriteLine($"没有名为 {name} 的封闭类型"); return 1; }
        foreach (var type in matches)
        {
            var layout = facts.Layouts.Of(type);
            if (layout is null) { Console.WriteLine($"{type}: 没有运行时布局"); continue; }
            Console.WriteLine($"{type}  instance_size=0x{layout.InstanceSize:x} actualSize=0x{layout.ActualSize:x} minimumAlignment={layout.MinimumAlignment} " +
                $"has_references={layout.HasReferences} {(layout.FromMetadata ? "（元数据）" : "（按运行时算法）")}");
            foreach (var f in layout.Fields) Console.WriteLine($"  +0x{f.Offset:x3} {f.Type} {f.Field.Name}");
            foreach (var f in layout.Statics) Console.WriteLine($"  static +0x{f.Offset:x3} {f.Type} {f.Field.Name}");
            foreach (var f in layout.ThreadStatics) Console.WriteLine($"  threadstatic +0x{f.Offset:x3} {f.Type} {f.Field.Name}");
        }
        return 0;
    }

    /// <summary>建立基础事实并写出 summary.json（检查结果、计时）。存在 Error 级违例时返回 1。</summary>
    private static int Facts(string binary, string metadata, string output)
    {
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        Directory.CreateDirectory(output);
        var summary = new
        {
            binarySha256 = facts.Model.Image.Sha256,
            metadataVersion = facts.Model.MetadataVersion,
            timings = facts.Timings,
            checks = facts.Checks.All,
        };
        File.WriteAllText(Path.Combine(output, "summary.json"), JsonSerializer.Serialize(summary, Json));
        FactsWriter.Write(facts, output);
        foreach (var check in facts.Checks.All)
        {
            var mark = check.Severity == "Info" ? "  " : check.Passed ? "✓ " : check.Severity == "Error" ? "✗ " : "! ";
            Console.WriteLine($"{mark}{check.Name}: {check.Violations}/{check.Total} — {check.Detail}");
            foreach (var sample in check.Samples) Console.WriteLine($"      {sample}");
        }
        return facts.Checks.AnyErrors ? 1 : 0;
    }
}
