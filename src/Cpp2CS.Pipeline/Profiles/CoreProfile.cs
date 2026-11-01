using Cpp2CS.Input;
using static Cpp2CS.Pipeline.RecoveryReport;

namespace Cpp2CS.Pipeline;

internal static class CoreProfile
{
    internal static RecoveryRunResult Run(RecoveryRequest request, Action<string>? progress)
    {
        void Log(string message) => progress?.Invoke(message);
        var manifest = new RunManifest(request);
        var facts = manifest.Step("facts", () => FactsBuilder.Build(request.Binary, request.Metadata, Log, options: request.Options));
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var selection = manifest.Step("selection", () => SelectionStage.Select(request, facts, Log));
        var batch = manifest.Step("recovery", () => RecoveryStage.RecoverMethods(selection.Targets, facts, types, request.Jobs, Log));
        var targets = batch.Targets;
        var summaries = new MethodSummaryService(batch.Recovery);
        for (var i = 0; i < targets.Length; i++) summaries.Seed(selection.Targets[i], targets[i]);
        var dependencies = new List<MethodRecoveryResult>();
        manifest.Step("dependencies", () =>
        {
            DependencyClosure.Complete(targets, dependencies, targets.ToDictionary(r => r.Method.Method), summaries);
            return dependencies.Count;
        });
        var results = targets.Concat(dependencies).ToArray();
        var dependencyMethods = dependencies.Select(r => r.Method.Method).ToHashSet();
        var skeleton = new Skeleton(facts.Model);
        skeleton.ApplyDeclarations(results);
        var emitter = new BodyEmitter(skeleton, types, diagnostics: request.Options.Diagnostics);
        var problems = emitter.Check(results.Where(r => r.Body is not null).Select(r => r.Body!), EmissionPolicy.Recovered);
        DependencyClosure.Validate(results, problems);
        var published = PublishStage.Run(results, dependencyMethods, emitter, problems);
        var emitted = published.Emitted;
        var partialEmitted = published.PartialEmitted;
        var emitProblems = published.Problems;
        var output = request.Output;
        Directory.CreateDirectory(output);
        var assemblies = Path.Combine(output, "assemblies");
        manifest.Step("publication", () => { skeleton.Write(assemblies); return emitted.Count; });
        ReportStage.WritePublications(output, results, skeleton);
        var bytes = results.Select(r => r.Entry).Distinct().ToDictionary(e => e, e => e == 0 ? 0 : checked((long)facts.Code.At(e)!.Size));
        ReportStage.WriteRecovery(output, results, bytes, dependencyMethods, emitProblems, partialEmitted,
            _ => "native-recovery", _ => null);
        ReportStage.WriteTraces(output, targets);
        ReportStage.WriteEmitted(output, emitted, skeleton, dependencyMethods);
        ReportStage.WriteUnselected(output, selection);
        var selectedSet = targets.ToHashSet();
        var report = Report(targets, emitted.Where(selectedSet.Contains).ToList(), emitProblems.Where(p => selectedSet.Contains(p.Key)).ToDictionary(),
            targets.Select(r => r.Entry).Distinct().ToDictionary(e => e, e => bytes[e]));
        var files = manifest.Step("decompile", () => DecompileStage.Write(request, facts, assemblies, emitted, partialEmitted, results, selection.Methods, Log));
        report.AppendLine($"core：依赖 {dependencies.Count}，部分体 {partialEmitted.Count}，C# {files} 个类型文件");
        File.WriteAllText(Path.Combine(output, "holes.txt"), report.ToString());
        var outcome = new RecoveryRunResult(output, report.ToString(), targets.Length, emitted.Count(selectedSet.Contains),
            emitProblems.Count(p => selectedSet.Contains(p.Key)), partialEmitted.Count);
        manifest.Complete(outcome);
        return outcome;
    }
}
