using System.Diagnostics;
using static Cpp2CS.Pipeline.RecoveryReport;
using Cpp2CS.Input;

namespace Cpp2CS.Pipeline;

/// <summary>恢复会话：按请求组织分析、依赖闭包和两类输出。</summary>
internal static class FullProfile
{
    public static RecoveryRunResult Run(RecoveryRequest request, Action<string>? progress = null)
    {
        request.Validate();
        var binary = request.Binary;
        var metadata = request.Metadata;
        var output = request.Output;
        var sourceLayout = request.SourceLayout;
        var accessorEvidence = request.VerifiedAccessors;
        var rejectedAccessors = request.RejectedAccessors;
        void Log(string message) => progress?.Invoke(message);
        var manifest = new RunManifest(request);
        var facts = manifest.Step("facts", () => FactsBuilder.Build(binary, metadata, Log, options: request.Options));
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var selection = manifest.Step("selection", () => SelectionStage.Select(request, facts, Log));
        var selected = selection.Targets;
        var methods = selection.Methods;
        var nativeEntries = selection.NativeEntries;
        var unselected = selection.Unselected;

        var watch = Stopwatch.StartNew();
        var batch = manifest.Step("recovery", () => RecoveryStage.RecoverMethods(selected, facts, types, request.Jobs, Log));
        var recovery = batch.Recovery;
        var summaries = new MethodSummaryService(recovery);
        for (var i = 0; i < selected.Length; i++) summaries.Seed(selected[i], batch.Targets[i]);
        var targets = batch.Targets;
        var stackCalls = batch.StackCalls;
        var bytes = targets.Select(r => r.Entry).Distinct().ToDictionary(e => e,
            e => checked((long)(facts.Code.At(e) ?? throw new InvalidDataException($"0x{e:x} 没有 L0 函数边界")).Size));
        Log($"L3 {watch.Elapsed.TotalSeconds:F1} s");

        watch.Restart();
        manifest.Begin("emission");
        var skeleton = new Skeleton(facts.Model);
        skeleton.ApplyDeclarations(targets);
        var emitter = new FullBodyEmitter(skeleton, types, request.Options.Diagnostics, request.Options.Readability);
        var closure = new AccessorRecovery(facts, types, summaries, emitter, targets, AutoPropertyManifest.ReadRejected(rejectedAccessors));
        skeleton.ApplyDeclarations(closure.All);
        var evidence = AccessorEvidence.Read(accessorEvidence);
        var descriptions = closure.Candidates.Values.ToDictionary(c => c.Method.Method, c => AccessorEvidence.Describe(facts, skeleton, c, emitter.Fingerprint(closure.All.Single(r => r.Method.Method == c.Method.Method).Body!)));
        var inlineDescriptions = closure.InlineCandidates.ToDictionary(p => p.Key, p => AccessorEvidence.Describe(facts, skeleton, p.Value.Method, emitter.Fingerprint(p.Value.Body!)));
        closure.Rewrite(types, emitter, c => evidence.Contains(descriptions[c.Method.Method]), m => evidence.Contains(inlineDescriptions[m]));
        var results = closure.All.ToArray();
        var dependencies = closure.Dependencies.Select(r => r.Method.Method).ToHashSet();
        foreach (var result in closure.Dependencies) bytes[result.Entry] = result.Entry == 0 ? 0 : checked((long)facts.Code.At(result.Entry)!.Size);
        var problems = closure.Problems;
        var published = PublishStage.Run(results, dependencies, emitter, problems);
        var emitted = published.Emitted;
        var partials = published.Partials;
        var partialEmitted = published.PartialEmitted;
        var emitProblems = published.Problems;
        Log($"CIL {watch.Elapsed.TotalSeconds:F1} s");
        manifest.End();

        Directory.CreateDirectory(output);
        ReportStage.WriteUnselected(output, selection);
        AutoPropertyManifest.Write(output, closure, rejectedAccessors);
        ReportStage.WriteTraces(output, targets);
        File.WriteAllLines(Path.Combine(output, "stack-methodinfo.tsv"),
            new[] { "entry\tsite\tstore\tsp\tslot\tmethod" }.Concat(stackCalls.Concat(recovery.StackCalls)
                .Select(c => $"0x{c.Entry:x}\t0x{c.Site:x}\t0x{c.Store:x}\t{c.Sp}\t{c.Slot}\t{c.Method}")
                .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)));
        ReportStage.WriteRecovery(output, results, bytes, dependencies, emitProblems, partialEmitted,
            r => closure.Synthesized.ContainsKey(r.Method.Method) ? "language-definition" : "native-recovery",
            r => closure.LanguageAccessors.ContainsKey(r.Method.Method) ? "language-definition" : null);

        var targetResults = targets.ToHashSet();
        var report = Report(targets, emitted.Where(targetResults.Contains).ToList(), emitProblems.Where(p => targetResults.Contains(p.Key)).ToDictionary(),
            targets.Select(r => r.Entry).Distinct().ToDictionary(e => e, e => bytes[e]));
        report.AppendLine($"范围审计：所选顶层类型（含嵌套类型）还有 {unselected.Count(m => nativeEntries.ContainsKey(m))} 个有原生入口的方法未入清单；详见 unselected-methods.tsv。上述比例仅代表所选方法，不能作为整个类的恢复率。");
        report.AppendLine($"F9 依赖访问器：{closure.Dependencies.Count}，已写出 {emitted.Count(r => dependencies.Contains(r.Method.Method))}；不计入范围方法/字节指标");
        report.AppendLine($"F9b 语言定义候选：{closure.LanguageAccessors.Count}，合成 {closure.Synthesized.Count}（有原生代码 {closure.Synthesized.Count(p => p.Key.Address != 0)}，无原生代码 {closure.Synthesized.Count(p => p.Key.Address == 0)}）；其余保留普通恢复体");
        report.AppendLine($"F9 可用候选：{descriptions.Count}，证据匹配 {descriptions.Values.Count(evidence.Contains)}，实际认回目标 {emitter.AccessorCalls.Values.Select(a => a.Method).Distinct().Count()}");
        report.AppendLine($"内联认回候选：{inlineDescriptions.Count}，证据匹配 {inlineDescriptions.Values.Count(evidence.Contains)}，认回调用点 {emitter.InlineCalls.Count}（被调方法 {emitter.InlineCalls.Values.Distinct().Count()} 个）");
        AccessorEvidence.Write(Path.Combine(output, "accessor-evidence-input.tsv"), descriptions.Values.Concat(inlineDescriptions.Values).Where(evidence.Contains));
        File.WriteAllLines(Path.Combine(output, "accessor-candidates.tsv"), descriptions.Values.Order(StringComparer.Ordinal));
        File.WriteAllLines(Path.Combine(output, "inline-candidates.tsv"), inlineDescriptions.Values.Order(StringComparer.Ordinal));
        File.WriteAllLines(Path.Combine(output, "accessor-calls.tsv"), emitted.SelectMany(r => AccessorRecovery.Fields(r.Body!)
            .Select(x => (x.Address, Accessor: x.Value switch { FieldValue f => f.Accessor, StaticFieldValue f => f.Accessor, _ => null }))
            .Where(x => x.Accessor is not null).Select(x => $"0x{r.Entry:x}\t{r.Method}\t0x{x.Address:x}\t0x{x.Accessor!.Method.Method.Address:x}\t{x.Accessor.Method}\t{(x.Accessor.Write ? "setter" : "getter")}\t{(x.Accessor.Method.Method.IsStatic ? "static" : "instance")}")));

        watch.Restart();
        var assemblies = Path.Combine(output, "assemblies");
        skeleton.Write(assemblies);
        ReportStage.WritePublications(output, results, skeleton);
        ReportStage.WriteEmitted(output, emitted, skeleton, dependencies);
        File.WriteAllText(Path.Combine(output, "holes.txt"), report.ToString());
        // C# 输出用的方法体（只写进反编译用的 assemblies-src，执行对照仍用 assemblies 里的原样 CIL）：
        // async 入口方法与 MoveNext 都有方法体时提升成 async/await（AsyncLifting），全部方法体再经 SourceRewriter 整理。
        var source = manifest.Step("source", () => SourceViewStage.WriteSource(request, facts, types, summaries, emitter, skeleton,
            emitted, partialEmitted, results, dependencies, methods, Log));
        report.AppendLine();
        report.AppendLine($"部分方法体：有洞的范围方法 {partials.Length} 个有部分方法体，写出 {partialEmitted.Count} / {partialEmitted.Sum(r => bytes[r.Entry])} 字节（洞写成 Cpp2CS.Unrecovered 标记；不计入指标）");
        report.AppendLine($"C# 整理：{source.Rewritten - source.Failures} / {source.Rewritten} 个方法体经 SourceRewriter 整理后写出");
        report.AppendLine($"async 提升：{source.Lifted} 个方法写成 async/await；未提升 {source.LiftFailures.Values.Sum()}（{string.Join("；", source.LiftFailures.OrderByDescending(p => p.Value).Take(8).Select(p => $"{p.Key} {p.Value}"))}）");
        report.AppendLine($"C#：{source.Files} 个类型文件（{(sourceLayout == "project" ? "按程序集/命名空间组织，包含范围内的类型声明" : "只含已写出方法或部分方法体所在的顶层类型")}；未恢复成员仍为骨架占位体），{watch.Elapsed.TotalSeconds:F1} s");
        File.WriteAllText(Path.Combine(output, "holes.txt"), report.ToString());
        var outcome = new RecoveryRunResult(output, report.ToString(), targets.Length, emitted.Count(r => targetResults.Contains(r)),
            emitProblems.Count(p => targetResults.Contains(p.Key)), partialEmitted.Count);
        manifest.Complete(outcome);
        return outcome;
    }

}
