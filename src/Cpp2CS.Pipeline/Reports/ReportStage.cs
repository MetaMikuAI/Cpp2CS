using System.Text.Json;
using System.Security.Cryptography;
using static Cpp2CS.Pipeline.RecoveryReport;

namespace Cpp2CS.Pipeline;

internal static class ReportStage
{
    public static void WritePublications(string output, MethodRecoveryResult[] results, Skeleton skeleton)
    {
        File.WriteAllLines(Path.Combine(output, "publication.jsonl"), results.Select(result =>
        {
            var method = skeleton.Method(result.Method.Method);
            return JsonSerializer.Serialize(new
            {
                address = $"0x{result.Entry:x}",
                method = result.Method.ToString(),
                assembly = method.Module.Name,
                token = method.MetadataToken.ToUInt32(),
                cil = method.HasBody ? Convert.ToHexString(SHA256.HashData(CilBodyFingerprint.Describe(method))) : null,
            }, Json);
        }));
    }

    public static void WriteTraces(string output, MethodRecoveryResult[] targets)
    {
        File.WriteAllLines(Path.Combine(output, "analysis.jsonl"), targets.Select(r => JsonSerializer.Serialize(new
        {
            entry = $"0x{r.Entry:x}",
            method = r.Method.ToString(),
            steps = r.Analyses,
            passes = r.Passes,
        }, Json)));
        File.WriteAllLines(Path.Combine(output, "rules.jsonl"), targets.SelectMany(r => r.Rules.Select(rule => JsonSerializer.Serialize(new
        {
            entry = $"0x{r.Entry:x}",
            method = r.Method.ToString(),
            rule.Rule,
            rule.Site,
            status = rule.Status.ToString(),
            rule.Code,
            rule.Detail,
            rule.Evidence,
        }, Json))));
        File.WriteAllLines(Path.Combine(output, "call-resolution.jsonl"), targets.SelectMany(r => r.Calls.Select(c => JsonSerializer.Serialize(new
        {
            entry = $"0x{r.Entry:x}",
            method = r.Method.ToString(),
            site = $"0x{c.Site:x}",
            c.NativeEntry,
            c.TypeVersion,
            c.Status,
            selected = c.Selected?.ToString(),
            candidates = c.Candidates.Select(p => new { method = p.Method.ToString(), p.Evidence, p.Rejection }),
        }, Json))));
    }

    public static void WriteRecovery(string output, MethodRecoveryResult[] results, IReadOnlyDictionary<ulong, long> bytes,
        IReadOnlySet<MethodDef> dependencies, IReadOnlyDictionary<MethodRecoveryResult, string> emitProblems,
        IReadOnlySet<MethodRecoveryResult> partialEmitted, Func<MethodRecoveryResult, string?> bodySource,
        Func<MethodRecoveryResult, string?> accessorProof)
    {
        using (var writer = new StreamWriter(Path.Combine(output, "recovery.jsonl")))
            foreach (var result in results)
            {
                var status = result.Declaration is not null ? "runtime-declaration" : result.Body is null ? "hole" : emitProblems.ContainsKey(result) ? "emit-failed" : "emitted";
                writer.WriteLine(JsonSerializer.Serialize(new
                {
                    address = $"0x{result.Entry:x}",
                    method = result.Method.ToString(),
                    status,
                    bytes = bytes[result.Entry],
                    dependency = dependencies.Contains(result.Method.Method),
                    bodySource = result.Declaration is not null ? "runtime-declaration" : result.Body is null ? null : bodySource(result),
                    declaration = result.Declaration?.ToString(),
                    platformImport = result.PlatformImport,
                    accessorProof = accessorProof(result),
                    holes = result.Holes.Select(h => new { address = $"0x{h.Address:x}", reason = h.Reason, derived = h.Derived, code = h.Code, category = h.Category, id = h.Id, causeId = h.CauseId }),
                    emitProblem = emitProblems.GetValueOrDefault(result),
                    partial = partialEmitted.Contains(result),
                    statements = result.Body?.Blocks.Sum(b => b.Statements.Count),
                    regions = result.Body?.Regions.Count,
                    features = result.Body is { } body ? Features(body) : null,
                }, Json));
            }

    }

    public static void WriteEmitted(string output, IReadOnlyList<MethodRecoveryResult> emitted, Skeleton skeleton,
        IReadOnlySet<MethodDef> dependencyMethods)
    {
        File.WriteAllLines(Path.Combine(output, "emitted.tsv"), emitted.Select(r =>
        {
            var top = Top(r.Method.Method.Owner);
            return $"{top.Assembly}\t{top.Namespace}\t{top.SimpleName}\t0x{r.Entry:x}\t{r.Method}\t0x{skeleton.Method(r.Method.Method).MetadataToken.ToUInt32():x8}\t{(dependencyMethods.Contains(r.Method.Method) ? "dependency" : "target")}";
        }));
    }

    public static void WriteUnselected(string output, SelectionStage.Selection selection)
    {
        File.WriteAllLines(Path.Combine(output, "unselected-methods.tsv"), new[] { "method\tdefinition_index\tkind\tnative_entries" }.Concat(selection.Unselected.Select(m =>
            $"{MethodRef.Open(m)}\t{m.Index}\t{(m.IsAbstract ? "abstract" : selection.NativeEntries.ContainsKey(m) ? "native-omitted" : "no-native-entry")}\t{string.Join(",", selection.NativeEntries.GetValueOrDefault(m, []).Select(e => $"0x{e:x}"))}")));
    }
}
