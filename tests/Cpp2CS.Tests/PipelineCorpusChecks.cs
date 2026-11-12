using System.Collections.Concurrent;
using System.Text;
using System.Text.Json;
using Cpp2CS.Pipeline;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Tests.Metrics;
using Mono.Cecil;

namespace Cpp2CS.Tests;

internal static class PipelineCorpusChecks
{
    public const string Command = "pipeline-corpus";
    public static int Run() => Run(true);
    private sealed class ConstructorAuditStage(IMethodStage<NativeFunction, ManagedBody> recovery) : IMethodStage<NativeFunction, ManagedBody>, IMethodTemplateSource
    {
        private readonly ConcurrentDictionary<MethodDef, StageResult<ManagedBody>> results = [];
        public GlobalFacts? Facts { get; private set; }
        public string Name => recovery.Name;
        public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context)
        {
            Facts = context.Facts;
            var result = recovery.Run(input, context);
            if (context.Method is { Name: ".ctor", IsStatic: false }) results.TryAdd(context.Method, result);
            return result;
        }
        public ManagedBody? GetBody(MethodDef method) => results.GetValueOrDefault(method) is Completed<ManagedBody> body ? body.Value : null;
        public Cpp2CS.Native.Terms.Reason? GetFailure(MethodDef method) => results.GetValueOrDefault(method) is Missing<ManagedBody> missing ? missing.Hole.Reason : null;
    }
    public static int WithoutSymbols() => Run(false);
    public static int WithoutAccessors() => Run(true, false);
    public static int WithoutConstructors() => Run(true, constructors: false);
    private static int Run(bool useSymbols, bool accessors = true, bool constructors = true)
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        {
            Console.WriteLine("跳过 Pipeline 定向检查：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。");
            return 0;
        }
        var checks = new Assertions();
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", !constructors ? "pipeline-corpus-constructors-disabled.local.output" : !accessors ? "pipeline-corpus-accessors-disabled.local.output"
            : useSymbols ? "pipeline-corpus.local.output" : "pipeline-corpus-nosymbols.local.output");
        var accessorAttempts = new ConcurrentBag<AccessorAttempt>();
        var constructorAttempts = new ConcurrentBag<ConstructorAttempt>();
        var recovery = new IntegerRecoveryStage(enableAccessorInlining: accessors, observeAccessors: accessorAttempts.Add, observeConstructors: constructorAttempts.Add, enableConstructorInlining: constructors);
        var audit = new ConstructorAuditStage(recovery);
        var report = new RecoverySession(recovery: audit).Run(new(
            Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a", "libil2cpp.so"),
            Path.Combine(corpus, "artifacts", "il2cppOutput", "data", "Metadata", "global-metadata.dat"), output)
        {
            // 两种配置使用同一套恢复与对照；无符号配置只依赖嵌入规格。
            Symbols = useSymbols ? Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a", "libil2cpp.dbg.so") : null,
            Jobs = Environment.ProcessorCount,
        });
        if (audit.Facts is { } facts)
        {
            var pointer = facts.Image.PointerWidth;
            var templates = new ConstructorTemplates(audit, new ManagedTypes(facts.Model, new FieldLayouts(facts.Spec, pointer, pointer), pointer));
            var inspected = facts.Model.Methods.Where(m => m is { Name: ".ctor", IsStatic: false }).Select(m => (Method: m, Result: templates.Get(m))).ToArray();
            File.WriteAllText(Path.Combine(output, "constructor-templates.local.json"), JsonSerializer.Serialize(inspected.Select(i => new
            {
                Method = RecoverySession.Identity(i.Method), Name = i.Method.ToString(),
                Fields = i.Result.Template?.Fields.Count, Overwritten = i.Result.Template?.Overwritten,
                Code = i.Result.Failure?.Code, Message = i.Result.Failure?.Message, Cause = i.Result.Failure?.Cause,
            }), new JsonSerializerOptions { WriteIndented = true }));
            Console.WriteLine($"构造模板普查：直线={inspected.Count(i => i.Result.Template is not null)}；覆盖写入={inspected.Sum(i => i.Result.Template?.Overwritten ?? 0)}；" +
                string.Join("，", inspected.Where(i => i.Result.Template is null).GroupBy(i => i.Result.Failure!.Message.Split('：')[0]).OrderBy(g => g.Key).Select(g => g.Key + "=" + g.Count())));
        }
        var byId = report.Methods.ToDictionary(m => m.Identity);
        var anchors = accessorAttempts.DistinctBy(a => (a.Access.Caller, a.Access.Position, a.Access.Field, a.Access.Kind))
            .OrderBy(a => RecoverySession.Identity(a.Access.Caller.Method), StringComparer.Ordinal)
            .ThenBy(a => a.Access.Position).ToArray();
        File.WriteAllText(Path.Combine(output, "accessors.local.json"), JsonSerializer.Serialize(anchors.Select(a => new
        {
            Caller = RecoverySession.Identity(a.Access.Caller.Method), Method = a.Access.Caller.Method.ToString(),
            a.Access.Position, Generic = a.Access.Field.Field.Owner.GenericParameters.Count != 0, Field = a.Access.Field.ToString(), Kind = a.Access.Kind.ToString(),
            Accessor = a.Answer.Method?.ToString(), AccessorIdentity = a.Answer.Method is { } selected ? RecoverySession.Identity(selected.Method) : null,
            Code = a.Answer.Failure?.Code ?? "Solved", None = a.Answer.NoneReason?.ToString(), a.Answer.Matches,
            Placement = a.Answer.Failure?.Cause?.Code,
            IncompleteCandidates = a.Answer.IncompleteCandidates.Select(candidate => new
            {
                Method = RecoverySession.Identity(candidate.Method), Name = candidate.Method.ToString(),
                Code = candidate.Failure?.Code, Message = candidate.Failure?.Message,
            }),
        }), new JsonSerializerOptions { WriteIndented = true }));
        Console.WriteLine("访问器锚点：" + anchors.Length + "；" + string.Join("，", anchors.GroupBy(a =>
            a.Answer.NoneReason?.ToString() ?? a.Answer.Failure?.Code ?? "Solved").OrderBy(g => g.Key).Select(g => g.Key + "=" + g.Count())));
        var genericAnchors = anchors.Where(a => a.Access.Field.Field.Owner.GenericParameters.Count != 0).ToArray();
        Console.WriteLine("泛型访问器锚点：" + genericAnchors.Length + "；" + string.Join("，", genericAnchors.GroupBy(a =>
            a.Answer.NoneReason?.ToString() ?? a.Answer.Failure?.Cause?.Code ?? a.Answer.Failure?.Code ?? "Solved")
            .OrderBy(g => g.Key).Select(g => g.Key + "=" + g.Count())));
        var constructorAnchors = constructorAttempts.DistinctBy(a => (a.Access.Caller, a.Access.Position, a.Access.Type, a.Access.Anchor))
            .OrderBy(a => RecoverySession.Identity(a.Access.Caller.Method), StringComparer.Ordinal).ThenBy(a => a.Access.Position).ToArray();
        File.WriteAllText(Path.Combine(output, "constructors.local.json"), JsonSerializer.Serialize(constructorAnchors.Select(a => new
        {
            Caller = RecoverySession.Identity(a.Access.Caller.Method), Method = a.Access.Caller.Method.ToString(),
            a.Access.Position, Type = a.Access.Type.ToString(), Anchor = a.Access.Anchor.ToString(),
            Constructor = a.Answer.Method?.ToString(), ConstructorIdentity = a.Answer.Method is { } selected ? RecoverySession.Identity(selected.Method) : null,
            Code = a.Answer.Failure?.Code ?? "Solved", Message = a.Answer.Failure?.Message,
            Arguments = a.Answer.Arguments.Select(v => v.ToString()), ConsumedWrites = a.Answer.Writes.Count,
            Candidates = a.Answer.Candidates.Select(candidate => new
            {
                Method = RecoverySession.Identity(candidate.Method.Method), Name = candidate.Method.ToString(),
                Fields = candidate.Template.Template?.Fields.Count, Overwritten = candidate.Template.Template?.Overwritten,
                Code = candidate.Template.Failure?.Code, Message = candidate.Template.Failure?.Message, candidate.Difference,
            }),
        }), new JsonSerializerOptions { WriteIndented = true }));
        foreach (var group in constructorAnchors.GroupBy(a => a.Access.Anchor).OrderBy(g => g.Key))
            Console.WriteLine($"构造锚点 {group.Key}：{group.Count()}；" + string.Join("，", group.GroupBy(a => a.Answer.Failure?.Code ?? "Solved")
                .OrderBy(g => g.Key).Select(g => g.Key + "=" + g.Count())));
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
                if (!metrics.TryAdd(id, IlMetrics.Compare(method, candidate, options, modelFactory, recovered?.WitnessCoverage)))
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
        checks.True(report.Methods.Where(m => m.Status == MethodStatus.Complete && metrics[m.Identity].Instances is not null)
            .All(m => m.WitnessCoverage == (m.HasValueTypeInstance ? Cpp2CS.Managed.GenericWitnessCoverage.ReferenceAndValue
                : Cpp2CS.Managed.GenericWitnessCoverage.ReferenceOnly)), "泛型定义的覆盖标记与代码地图中的值实例及恢复见证一致");
        File.WriteAllText(Path.Combine(output, "comparison.local.json"), IlMetrics.Json(comparison));
        checks.True(report.Summary.ProgramErrors.Length == 0, "没有程序错误：" + string.Join("；", report.Summary.ProgramErrors.Take(3)));
        checks.True(report.Summary.ContractFailures.Length == 0, "没有输出层契约失败：" + string.Join("；", report.Summary.ContractFailures.Take(3)));
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

internal static class PipelineWithoutSymbolsCorpusChecks
{
    public const string Command = "pipeline-corpus-nosymbols";
    public static int Run() => PipelineCorpusChecks.WithoutSymbols();
}

internal static class PipelineWithoutAccessorsCorpusChecks
{
    public const string Command = "pipeline-corpus-accessors-disabled";
    public static int Run() => PipelineCorpusChecks.WithoutAccessors();
}

internal static class PipelineWithoutConstructorsCorpusChecks
{
    public const string Command = "pipeline-corpus-constructors-disabled";
    public static int Run() => PipelineCorpusChecks.WithoutConstructors();
}
