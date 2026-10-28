using System.Diagnostics;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Cpp2CS.Structure;
using Cpp2CS.Analysis;

namespace Cpp2CS.Pipeline;

public static partial class RecoverySession
{
    private sealed record SourceResult(int Rewritten, int Failures, int Lifted, Dictionary<string, int> LiftFailures, int Files);

    private static SourceResult WriteSource(RecoveryRequest request, ProgramFacts facts, ManagedTypes types, MethodSummaryService summaries,
        BodyEmitter emitter, Skeleton skeleton, List<MethodRecoveryResult> emitted, HashSet<MethodRecoveryResult> partialEmitted,
        MethodRecoveryResult[] results, HashSet<MethodDef> dependencies, MethodDef[] methods, Action<string> Log)
    {
        var output = request.Output;
        var noSource = request.NoSource;
        var sourceLayout = request.SourceLayout;
        var list = request.Methods;
        var namespaces = request.Namespaces;
        var assembliesFilter = request.Assemblies;
        var all = request.All || assembliesFilter is not null;
        var written = emitted.Concat(partialEmitted).Where(r => !dependencies.Contains(r.Method.Method)).GroupBy(r => r.Method.Method).ToDictionary(g => g.Key, g => g.First().Body ?? g.First().Partial!);
        var sourceBodies = new Dictionary<MethodDef, ManagedBody>(written);
        var liftFailures = new Dictionary<string, int>();
        var liftRows = new List<string> { "entry\tmethod\tstatus\treason" };
        var lifted = new HashSet<MethodDef>();
        var families = StateMachineFamilies.Read(written);
        File.WriteAllLines(Path.Combine(output, "state-machine-families.jsonl"), families.Select(f => JsonSerializer.Serialize(new
        {
            kickoff = f.Kickoff.ToString(), machine = f.Machine.ToString(), moveNext = f.MoveNext?.ToString(), f.Status, f.Reason,
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
            if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1") Log($"  [未提升] {method}：{reason}");
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
            method = p.Key.ToString(), steps = p.Value.Passes,
        }, Json)));
        File.WriteAllText(Path.Combine(output, "summaries.json"), JsonSerializer.Serialize(new
        {
            summaries.Count, summaries.DiscoveryRounds, summaries.AnalysisRuns,
        }, Json));
        File.WriteAllLines(Path.Combine(output, "source-library-calls.tsv"), prepared.Values.SelectMany(p => p.LibraryEvidence));
        if (Environment.GetEnvironmentVariable("CPP2CS_SOURCE_DUMP") is { Length: > 0 } dump)
            foreach (var statement in rewritten.Values.SelectMany(b => b.Blocks).SelectMany(b => b.Statements).Where(s => s.ToString().Contains(dump, StringComparison.Ordinal)))
                Log($"  [整理后] {statement}");
        var sourceProblems = emitter.Emit(rewritten.Values, EmissionPolicy.Source);
        if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1")
            foreach (var (method, body) in rewritten.Where(p => sourceProblems.ContainsKey(p.Value))) Log($"  [整理后写不出] {method}：{sourceProblems[body]}");
        // 整理后写不出的退回整理前（提升过的入口方法退回提升后的方法体）。
        var fallback = rewritten.Where(p => sourceProblems.ContainsKey(p.Value)).Select(p => sourceBodies[p.Key]).ToArray();
        var liftProblems = emitter.Emit(fallback, EmissionPolicy.Source);
        lifted.RemoveWhere(m => sourceProblems.ContainsKey(rewritten[m]) && liftProblems.ContainsKey(sourceBodies[m]));
        var sourceAssemblies = Path.Combine(output, "assemblies-src");
        skeleton.Write(sourceAssemblies);
        var sources = Path.Combine(output, "src");
        if (Directory.Exists(sources)) Directory.Delete(sources, true);
        Directory.CreateDirectory(sources);
        var invalid = Path.GetInvalidFileNameChars();
        var files = 0;
        var sourceTypes = sourceLayout == "project"
            ? facts.Model.Types.Where(t => t.DeclaringType is null && (list is not null ? methods.Any(m => Top(m.Owner) == t)
                : (all || InNamespaces(t, namespaces)) && (assembliesFilter is null || assembliesFilter.Contains(t.Assembly, StringComparer.Ordinal))))
            : emitted.Concat(partialEmitted).Concat(results.Where(r => r.Declaration is not null)).Select(r => Top(r.Method.Method.Owner)).Distinct();
        var sourceGroups = sourceTypes.GroupBy(t => t.Assembly).ToDictionary(g => g.Key, g => g.Select(t => (t.Namespace, t.SimpleName)).ToHashSet());
        var sourceAssemblyNames = sourceLayout == "project" && all
            ? facts.Model.Assemblies.Select(a => a.Name).Where(a => assembliesFilter is null || assembliesFilter.Contains(a, StringComparer.Ordinal))
            : sourceGroups.Keys.AsEnumerable();
        foreach (var assemblyName in sourceAssemblyNames.Where(_ => !noSource))
        {
            var wanted = sourceGroups.GetValueOrDefault(assemblyName) ?? [];
            if (sourceLayout == "project")
            {
                var count = SourceProject.Write(Path.Combine(sourceAssemblies, assemblyName), sourceAssemblies, sources,
                    t => all || wanted.Contains((t.Namespace, t.Name)));
                files += count;
                Log($"C# {assemblyName}：{count} 个类型文件，累计 {files}");
                continue;
            }
            foreach (var source in Decompilation.Decompile(Path.Combine(sourceAssemblies, assemblyName), sourceAssemblies,
                t => wanted.Contains((t.Namespace, t.Name)) || t.FullName == "Cpp2CS.NativeImports", false, recoveringBodies: true))
            {
                File.WriteAllText(Path.Combine(sources, new string((assemblyName + "_" + source.TypeName).Select(c => invalid.Contains(c) ? '_' : c).ToArray()) + ".cs"), source.Source);
                files++;
            }
        }
        File.WriteAllLines(Path.Combine(output, "source-status.jsonl"), rewritten.Select(p => JsonSerializer.Serialize(new
        {
            method = p.Key.ToString(),
            status = reductions[p.Key].Status != IterationStatus.Stable ? "fallback" : !sourceProblems.ContainsKey(p.Value) ? "rewritten" : !liftProblems.ContainsKey(sourceBodies[p.Key]) ? "fallback" : "preserved-cil",
            rewriteProblem = reductions[p.Key].Status != IterationStatus.Stable ? "source.reduction-not-converged" : sourceProblems.GetValueOrDefault(p.Value)?.Message,
            fallbackProblem = liftProblems.GetValueOrDefault(sourceBodies[p.Key])?.Message,
            asyncLifted = lifted.Contains(p.Key),
            reductionRounds = reductions[p.Key].Rounds, reductionStatus = reductions[p.Key].Status.ToString(),
            compile = "not-run", execution = "not-run",
        }, Json)));
        return new(rewritten.Count, rewritten.Count(p => sourceProblems.ContainsKey(p.Value) || reductions[p.Key].Status != IterationStatus.Stable), lifted.Count, liftFailures, files);
    }
}
