using System.Diagnostics;
using Cpp2CS.Input;
using static Cpp2CS.Pipeline.RecoveryReport;

namespace Cpp2CS.Pipeline;

/// <summary>一个阶段：名称、是否写出文件、执行体。不写文件的阶段可以在没有运行清单时执行（执行对照）。</summary>
internal sealed record Stage(string Name, bool Writes, Action<RecoveryRun> Run);

/// <summary>
/// core 与 full 的阶段表。facts、selection、recovery 两者共用；core 之后是依赖闭包、写出、发布、反编译，
/// full 之后是访问器闭包与写出、报告、发布、源码视图。每个阶段内部的次序与原过程式脚本逐条相同。
/// </summary>
internal static class StageTables
{
    public static Stage[] For(string profile) => profile == "core" ? Core : Full;

    public static readonly Stage[] Core =
    [
        new("facts", false, Facts),
        new("selection", false, Selection),
        new("recovery", false, Recovery),
        new("dependencies", false, CoreDependencies),
        new("emission", false, CoreEmission),
        new("publication", true, CorePublication),
        new("decompile", true, CoreDecompile),
    ];

    public static readonly Stage[] Full =
    [
        new("facts", false, Facts),
        new("selection", false, Selection),
        new("recovery", false, Recovery),
        new("emission", false, FullEmission),
        new("reports", true, FullReports),
        new("publication", true, FullPublication),
        new("source", true, FullSource),
    ];

    private static void Facts(RecoveryRun run)
    {
        var request = run.Request;
        run.Facts = run.Step("facts", () => FactsBuilder.Build(request.Binary, request.Metadata, run.Log, options: request.Options));
        run.Types = new ManagedTypes(run.Facts.Model, run.Facts.Layouts);
    }

    private static void Selection(RecoveryRun run) => run.Selection = run.Step("selection", () => SelectionStage.Select(run.Request, run.Facts, run.Log));

    private static void Recovery(RecoveryRun run)
    {
        var watch = Stopwatch.StartNew();
        var selected = run.Selection.Targets;
        run.Batch = run.Step("recovery", () => RecoveryStage.RecoverMethods(selected, run.Facts, run.Types, run.Request.Jobs, run.Log));
        run.Summaries = new MethodSummaryService(run.Batch.Recovery);
        for (var i = 0; i < selected.Length; i++) run.Summaries.Seed(selected[i], run.Targets[i]);
        run.Log($"L3 {watch.Elapsed.TotalSeconds:F1} s");
    }

    // ---------- core ----------

    private static void CoreDependencies(RecoveryRun run)
    {
        var targets = run.Targets;
        var dependencies = new List<MethodRecoveryResult>();
        run.Step("dependencies", () =>
        {
            DependencyClosure.Complete(targets, dependencies, targets.ToDictionary(r => r.Method.Method), run.Summaries);
            return dependencies.Count;
        });
        run.Results = targets.Concat(dependencies).ToArray();
        run.Dependencies = dependencies.Select(r => r.Method.Method).ToHashSet();
        run.DependencyCount = dependencies.Count;
    }

    private static void CoreEmission(RecoveryRun run)
    {
        var results = run.Results;
        run.Skeleton = new Skeleton(run.Facts.Model);
        run.Skeleton.ApplyDeclarations(results);
        run.Emitter = new BodyEmitter(run.Skeleton, run.Types, diagnostics: run.Request.Options.Diagnostics);
        var problems = run.Problems = run.Emitter.Check(results.Where(r => r.Body is not null).Select(r => r.Body!), EmissionPolicy.Recovered);
        DependencyClosure.Validate(results, problems);
        run.Published = PublishStage.Run(results, run.Dependencies, run.Emitter, problems);
    }

    private static void CorePublication(RecoveryRun run)
    {
        var (request, facts, results, targets, published) = (run.Request, run.Facts, run.Results, run.Targets, run.Published);
        var output = request.Output;
        Directory.CreateDirectory(output);
        var assemblies = Path.Combine(output, "assemblies");
        run.Step("publication", () => { run.Skeleton.Write(assemblies); return published.Emitted.Count; });
        ReportStage.WritePublications(output, results, run.Skeleton);
        run.Bytes = results.Select(r => r.Entry).Distinct().ToDictionary(e => e, e => e == 0 ? 0 : checked((long)facts.Code.At(e)!.Size));
        ReportStage.WriteRecovery(output, results, run.Bytes, run.Dependencies, published.Problems, published.PartialEmitted,
            _ => "native-recovery", _ => null);
        ReportStage.WriteTraces(output, targets);
        ReportStage.WriteEmitted(output, published.Emitted, run.Skeleton, run.Dependencies);
        ReportStage.WriteUnselected(output, run.Selection);
        var selectedSet = targets.ToHashSet();
        run.Report = Report(targets, published.Emitted.Where(selectedSet.Contains).ToList(), published.Problems.Where(p => selectedSet.Contains(p.Key)).ToDictionary(),
            targets.Select(r => r.Entry).Distinct().ToDictionary(e => e, e => run.Bytes[e]));
    }

    private static void CoreDecompile(RecoveryRun run)
    {
        var (request, targets, published) = (run.Request, run.Targets, run.Published);
        var assemblies = Path.Combine(request.Output, "assemblies");
        var files = run.Step("decompile", () => DecompileStage.Write(request, run.Facts, assemblies, published.Emitted, published.PartialEmitted,
            run.Results, run.Selection.Methods, run.Log));
        run.Report.AppendLine($"core：依赖 {run.DependencyCount}，部分体 {published.PartialEmitted.Count}，C# {files} 个类型文件");
        File.WriteAllText(Path.Combine(request.Output, "holes.txt"), run.Report.ToString());
        var selectedSet = targets.ToHashSet();
        run.Outcome = new RecoveryRunResult(request.Output, run.Report.ToString(), targets.Length, published.Emitted.Count(selectedSet.Contains),
            published.Problems.Count(p => selectedSet.Contains(p.Key)), published.PartialEmitted.Count);
    }

    // ---------- full ----------

    private static void FullEmission(RecoveryRun run)
    {
        var (request, facts, types, targets) = (run.Request, run.Facts, run.Types, run.Targets);
        run.Bytes = targets.Select(r => r.Entry).Distinct().ToDictionary(e => e,
            e => checked((long)(facts.Code.At(e) ?? throw new InvalidDataException($"0x{e:x} 没有 L0 函数边界")).Size));
        var watch = Stopwatch.StartNew();
        run.Begin("emission");
        var skeleton = run.Skeleton = new Skeleton(facts.Model);
        skeleton.ApplyDeclarations(targets);
        var emitter = new FullBodyEmitter(skeleton, types, request.Options.Diagnostics, request.Options.Readability);
        run.Emitter = emitter;
        var closure = run.Closure = new AccessorRecovery(facts, types, run.Summaries, emitter, targets, AutoPropertyManifest.ReadRejected(request.RejectedAccessors));
        skeleton.ApplyDeclarations(closure.All);
        var evidence = run.Evidence = AccessorEvidence.Read(request.VerifiedAccessors);
        var descriptions = run.Descriptions = closure.Candidates.Values.ToDictionary(c => c.Method.Method, c => AccessorEvidence.Describe(facts, skeleton, c, emitter.Fingerprint(closure.All.Single(r => r.Method.Method == c.Method.Method).Body!)));
        var inlineDescriptions = run.InlineDescriptions = closure.InlineCandidates.ToDictionary(p => p.Key, p => AccessorEvidence.Describe(facts, skeleton, p.Value.Method, emitter.Fingerprint(p.Value.Body!)));
        closure.Rewrite(types, emitter, c => evidence.Contains(descriptions[c.Method.Method]), m => evidence.Contains(inlineDescriptions[m]));
        run.Results = closure.All.ToArray();
        run.Dependencies = closure.Dependencies.Select(r => r.Method.Method).ToHashSet();
        foreach (var result in closure.Dependencies) run.Bytes[result.Entry] = result.Entry == 0 ? 0 : checked((long)facts.Code.At(result.Entry)!.Size);
        run.Problems = closure.Problems;
        run.Published = PublishStage.Run(run.Results, run.Dependencies, emitter, closure.Problems);
        run.Log($"CIL {watch.Elapsed.TotalSeconds:F1} s");
        run.End();
    }
    private static void FullReports(RecoveryRun run)
    {
        var (request, facts, targets, published, closure) = (run.Request, run.Facts, run.Targets, run.Published, run.Closure!);
        var (output, rejectedAccessors) = (request.Output, request.RejectedAccessors);
        var (emitted, partialEmitted, emitProblems) = (published.Emitted, published.PartialEmitted, published.Problems);
        var (dependencies, bytes, emitter, evidence) = (run.Dependencies, run.Bytes, (FullBodyEmitter)run.Emitter, run.Evidence);
        var unselected = run.Selection.Unselected;
        var nativeEntries = run.Selection.NativeEntries;
        Directory.CreateDirectory(output);
        ReportStage.WriteUnselected(output, run.Selection);
        AutoPropertyManifest.Write(output, closure, rejectedAccessors);
        ReportStage.WriteTraces(output, targets);
        File.WriteAllLines(Path.Combine(output, "stack-methodinfo.tsv"),
            new[] { "entry\tsite\tstore\tsp\tslot\tmethod" }.Concat(run.Batch.StackCalls.Concat(run.Batch.Recovery.StackCalls)
                .Select(c => $"0x{c.Entry:x}\t0x{c.Site:x}\t0x{c.Store:x}\t{c.Sp}\t{c.Slot}\t{c.Method}")
                .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)));
        ReportStage.WriteRecovery(output, run.Results, bytes, dependencies, emitProblems, partialEmitted,
            r => closure.Synthesized.ContainsKey(r.Method.Method) ? "language-definition" : "native-recovery",
            r => closure.LanguageAccessors.ContainsKey(r.Method.Method) ? "language-definition" : null);

        var targetResults = targets.ToHashSet();
        var report = run.Report = Report(targets, emitted.Where(targetResults.Contains).ToList(), emitProblems.Where(p => targetResults.Contains(p.Key)).ToDictionary(),
            targets.Select(r => r.Entry).Distinct().ToDictionary(e => e, e => bytes[e]));
        report.AppendLine($"范围审计：所选顶层类型（含嵌套类型）还有 {unselected.Count(m => nativeEntries.ContainsKey(m))} 个有原生入口的方法未入清单；详见 unselected-methods.tsv。上述比例仅代表所选方法，不能作为整个类的恢复率。");
        report.AppendLine($"F9 依赖访问器：{closure.Dependencies.Count}，已写出 {emitted.Count(r => dependencies.Contains(r.Method.Method))}；不计入范围方法/字节指标");
        report.AppendLine($"F9b 语言定义候选：{closure.LanguageAccessors.Count}，合成 {closure.Synthesized.Count}（有原生代码 {closure.Synthesized.Count(p => p.Key.Address != 0)}，无原生代码 {closure.Synthesized.Count(p => p.Key.Address == 0)}）；其余保留普通恢复体");
        report.AppendLine($"F9 可用候选：{run.Descriptions.Count}，证据匹配 {run.Descriptions.Values.Count(evidence.Contains)}，实际认回目标 {emitter.AccessorCalls.Values.Select(a => a.Method).Distinct().Count()}");
        report.AppendLine($"内联认回候选：{run.InlineDescriptions.Count}，证据匹配 {run.InlineDescriptions.Values.Count(evidence.Contains)}，认回调用点 {emitter.InlineCalls.Count}（被调方法 {emitter.InlineCalls.Values.Distinct().Count()} 个）");
        AccessorEvidence.Write(Path.Combine(output, "accessor-evidence-input.tsv"), run.Descriptions.Values.Concat(run.InlineDescriptions.Values).Where(evidence.Contains));
        File.WriteAllLines(Path.Combine(output, "accessor-candidates.tsv"), run.Descriptions.Values.Order(StringComparer.Ordinal));
        File.WriteAllLines(Path.Combine(output, "inline-candidates.tsv"), run.InlineDescriptions.Values.Order(StringComparer.Ordinal));
        File.WriteAllLines(Path.Combine(output, "accessor-calls.tsv"), emitted.SelectMany(r => AccessorRecovery.Fields(r.Body!)
            .Select(x => (x.Address, Accessor: x.Value switch { FieldValue f => f.Accessor, StaticFieldValue f => f.Accessor, _ => null }))
            .Where(x => x.Accessor is not null).Select(x => $"0x{r.Entry:x}\t{r.Method}\t0x{x.Address:x}\t0x{x.Accessor!.Method.Method.Address:x}\t{x.Accessor.Method}\t{(x.Accessor.Write ? "setter" : "getter")}\t{(x.Accessor.Method.Method.IsStatic ? "static" : "instance")}")));
    }

    private static void FullPublication(RecoveryRun run)
    {
        var output = run.Request.Output;
        run.Clock.Restart();
        run.Skeleton.Write(Path.Combine(output, "assemblies"));
        ReportStage.WritePublications(output, run.Results, run.Skeleton);
        ReportStage.WriteEmitted(output, run.Published.Emitted, run.Skeleton, run.Dependencies);
        File.WriteAllText(Path.Combine(output, "holes.txt"), run.Report.ToString());
    }

    private static void FullSource(RecoveryRun run)
    {
        var (request, targets, published, report) = (run.Request, run.Targets, run.Published, run.Report);
        var output = request.Output;
        // C# 输出用的方法体（只写进反编译用的 assemblies-src，执行对照仍用 assemblies 里的原样 CIL）：
        // async 入口方法与 MoveNext 都有方法体时提升成 async/await（AsyncLifting），全部方法体再经 SourceRewriter 整理。
        var source = run.Step("source", () => SourceViewStage.WriteSource(request, run.Facts, run.Types, run.Summaries, run.Emitter, run.Skeleton,
            published.Emitted, published.PartialEmitted, run.Results, run.Dependencies, run.Selection.Methods, run.Log));
        report.AppendLine();
        report.AppendLine($"部分方法体：有洞的范围方法 {published.Partials.Length} 个有部分方法体，写出 {published.PartialEmitted.Count} / {published.PartialEmitted.Sum(r => run.Bytes[r.Entry])} 字节（洞写成 Cpp2CS.Unrecovered 标记；不计入指标）");
        report.AppendLine($"C# 整理：{source.Rewritten - source.Failures} / {source.Rewritten} 个方法体经 SourceRewriter 整理后写出");
        report.AppendLine($"async 提升：{source.Lifted} 个方法写成 async/await；未提升 {source.LiftFailures.Values.Sum()}（{string.Join("；", source.LiftFailures.OrderByDescending(p => p.Value).Take(8).Select(p => $"{p.Key} {p.Value}"))}）");
        report.AppendLine($"C#：{source.Files} 个类型文件（{(request.SourceLayout == "project" ? "按程序集/命名空间组织，包含范围内的类型声明" : "只含已写出方法或部分方法体所在的顶层类型")}；未恢复成员仍为骨架占位体），{run.Clock.Elapsed.TotalSeconds:F1} s");
        File.WriteAllText(Path.Combine(output, "holes.txt"), report.ToString());
        var targetResults = targets.ToHashSet();
        run.Outcome = new RecoveryRunResult(output, report.ToString(), targets.Length, published.Emitted.Count(r => targetResults.Contains(r)),
            published.Problems.Count(p => targetResults.Contains(p.Key)), published.PartialEmitted.Count);
    }
}
