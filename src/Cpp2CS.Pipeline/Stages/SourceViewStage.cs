using System.Text.Json;
using Cpp2CS.Facts;
using static Cpp2CS.Pipeline.RecoveryReport;

namespace Cpp2CS.Pipeline;

internal static class SourceViewStage
{
    internal sealed record SourceResult(int Rewritten, int Failures, int Lifted, Dictionary<string, int> LiftFailures, int Files);

    internal static SourceResult WriteSource(RecoveryRequest request, ProgramFacts facts, ManagedTypes types, MethodSummaryService summaries,
        BodyEmitter emitter, Skeleton skeleton, List<MethodRecoveryResult> emitted, HashSet<MethodRecoveryResult> partialEmitted,
        MethodRecoveryResult[] results, HashSet<MethodDef> dependencies, MethodDef[] methods, Action<string> Log)
    {
        var output = request.Output;
        var written = emitted.Concat(partialEmitted).Where(r => !dependencies.Contains(r.Method.Method)).GroupBy(r => r.Method.Method).ToDictionary(g => g.Key, g => g.First().Body ?? g.First().Partial!);
        var sourceBodies = new Dictionary<MethodDef, ManagedBody>(written);
        var liftFailures = new Dictionary<string, int>();
        var liftRows = new List<string> { "entry\tmethod\tstatus\treason" };
        var lifted = new HashSet<MethodDef>();
        var families = StateMachineFamilies.Read(written);
        File.WriteAllLines(Path.Combine(output, "state-machine-families.jsonl"), families.Select(f => JsonSerializer.Serialize(new
        {
            kickoff = f.Kickoff.ToString(),
            machine = f.Machine.ToString(),
            moveNext = f.MoveNext?.ToString(),
            f.Status,
            f.Reason,
        }, Json)));
        foreach (var family in families)
        {
            var method = family.Kickoff.Method;
            var kickoff = family.KickoffBody!;
            if (family.MoveNextBody is not { } machineBody) continue;
            if (AsyncLifting.Lift(kickoff, machineBody, out var reason) is { } body)
            {
                sourceBodies[method] = body; lifted.Add(method);
                liftRows.Add($"0x{method.Address:x}\t{method}\tlifted\t");
                continue;
            }
            liftRows.Add($"0x{method.Address:x}\t{method}\tpreserved\t{reason}");
            if (request.Options.Diagnostics.Emit) Log($"  [未提升] {method}：{reason}");
            var key = string.Join(" ", reason.Split(' ').Skip(reason.StartsWith("async", StringComparison.Ordinal) ? 2 : 0).Take(1));
            liftFailures[key] = liftFailures.GetValueOrDefault(key) + 1;
        }
        File.WriteAllLines(Path.Combine(output, "async-lifting.tsv"), liftRows);
        var libraryIndex = new SourceLibraryIndex(facts);
        var prepared = summaries.Complete(sourceBodies.Keys.ToArray(),
            (method, catalog) => SourcePreparation.Run(sourceBodies[method], facts, types, catalog, libraryIndex));
        var reductions = prepared.ToDictionary(p => p.Key, p => p.Value.Reduction);
        var rewritten = prepared.ToDictionary(p => p.Key, p => p.Value.Body);
        File.WriteAllLines(Path.Combine(output, "source-passes.jsonl"), prepared.Select(p => JsonSerializer.Serialize(new
        {
            method = p.Key.ToString(),
            steps = p.Value.Passes,
        }, Json)));
        File.WriteAllText(Path.Combine(output, "summaries.json"), JsonSerializer.Serialize(new
        {
            summaries.Count,
            summaries.DiscoveryRounds,
            summaries.AnalysisRuns,
        }, Json));
        File.WriteAllLines(Path.Combine(output, "source-library-calls.tsv"), prepared.Values.SelectMany(p => p.LibraryEvidence));
        if (request.Options.Diagnostics.SourceDump is { Length: > 0 } dump)
            foreach (var statement in rewritten.Values.SelectMany(b => b.Blocks).SelectMany(b => b.Statements).Where(s => s.ToString().Contains(dump, StringComparison.Ordinal)))
                Log($"  [整理后] {statement}");
        var sourceProblems = emitter.Check(rewritten.Values, EmissionPolicy.Source);
        if (request.Options.Diagnostics.Emit)
            foreach (var (method, body) in rewritten.Where(p => sourceProblems.ContainsKey(p.Value))) Log($"  [整理后写不出] {method}：{sourceProblems[body]}");
        // 整理后写不出的退回整理前（提升过的入口方法退回提升后的方法体）。
        var fallback = rewritten.Where(p => sourceProblems.ContainsKey(p.Value)).Select(p => sourceBodies[p.Key]).ToArray();
        var liftProblems = emitter.Check(fallback, EmissionPolicy.Source);
        lifted.RemoveWhere(m => sourceProblems.ContainsKey(rewritten[m]) && liftProblems.ContainsKey(sourceBodies[m]));
        var publication = new BodyPublication(emitter);
        publication.Publish(rewritten.Where(p => !sourceProblems.ContainsKey(p.Value)).Select(p => p.Value), EmissionPolicy.Source);
        publication.Publish(fallback.Where(b => !liftProblems.ContainsKey(b)), EmissionPolicy.Source);
        var sourceAssemblies = Path.Combine(output, "assemblies-src");
        skeleton.Write(sourceAssemblies);
        var files = DecompileStage.Write(request, facts, sourceAssemblies, emitted, partialEmitted, results, methods, Log);
        File.WriteAllLines(Path.Combine(output, "source-status.jsonl"), rewritten.Select(p => JsonSerializer.Serialize(new
        {
            method = p.Key.ToString(),
            status = reductions[p.Key].Status != IterationStatus.Stable ? "fallback" : !sourceProblems.ContainsKey(p.Value) ? "rewritten" : !liftProblems.ContainsKey(sourceBodies[p.Key]) ? "fallback" : "preserved-cil",
            rewriteProblem = reductions[p.Key].Status != IterationStatus.Stable ? "source.reduction-not-converged" : sourceProblems.GetValueOrDefault(p.Value)?.Message,
            fallbackProblem = liftProblems.GetValueOrDefault(sourceBodies[p.Key])?.Message,
            asyncLifted = lifted.Contains(p.Key),
            reductionRounds = reductions[p.Key].Rounds,
            reductionStatus = reductions[p.Key].Status.ToString(),
            compile = "not-run",
            execution = "not-run",
        }, Json)));
        return new(rewritten.Count, rewritten.Count(p => sourceProblems.ContainsKey(p.Value) || reductions[p.Key].Status != IterationStatus.Stable), lifted.Count, liftFailures, files);
    }
}
