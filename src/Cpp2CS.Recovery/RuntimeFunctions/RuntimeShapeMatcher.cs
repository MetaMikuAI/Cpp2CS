using System.Collections.Concurrent;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.RuntimeFunctions;

/// <summary>完整形状与调用身份共同复核；同形且直接被调地址逐项相同的入口可作为同义包装。</summary>
public static class RuntimeShapeMatcher
{
    private sealed record Candidate(ulong Entry, RuntimeReferenceShape? Shape);
    public static IReadOnlyList<(ulong Entry, RuntimeFunctionLocation Location)> Locate(IImage image,
        RuntimeFunctionCatalog catalog, RuntimeShapeCatalog references, Func<ulong, NativeFunction?> lift,
        Func<CallTarget, CallTarget> normalize, IDictionary<string, string>? missingReasons = null, int jobs = 1, RuntimeUsageEvidence? usageEvidence = null)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(jobs, 1);
        var ranges = image.Functions.ToDictionary(f => f.Start);
        var shapeEntries = references.Entries.Where(e => e.Shape is not null).ToArray();
        var lengths = shapeEntries.Select(e => e.Length).ToHashSet();
        var byShape = shapeEntries.GroupBy(e => (e.Length, e.Shape)).ToDictionary(g => g.Key, g => g.ToArray());
        var candidatesByReference = references.Entries.ToDictionary(e => e, _ => new ConcurrentBag<Candidate>());
        // 只缓存摘要，避免持有全映像的项表与快照；锚点、候选和被调复核共用缓存。
        var summaries = new ConcurrentDictionary<ulong, Lazy<RuntimeReferenceShape?>>();
        RuntimeReferenceShape? Shape(ulong entry) => summaries.GetOrAdd(entry, key => new(() =>
        {
            if (!ranges.TryGetValue(key, out var range) || !range.HasConsistentExtent) return null;
            var function = lift(key);
            return function is null ? null : RuntimeReferenceShape.Create(function, normalize, image);
        })).Value;
        var resolver = new RuntimeExportAnchorResolver(image, references, Shape);
        var resolved = new Dictionary<string, ulong?>(StringComparer.Ordinal);
        var anchorFailures = new Dictionary<string, string>(StringComparer.Ordinal);
        void Resolve(string? anchor)
        {
            if (anchor is null || resolved.ContainsKey(anchor)) return;
            resolved.Add(anchor, resolver.Resolve(anchor, out var reason));
            if (reason is not null) anchorFailures.Add(anchor, reason);
        }
        void ResolveCallee(RuntimeCalleeShape callee)
        {
            Resolve(callee.Anchor);
            foreach (var child in callee.Callees ?? []) ResolveCallee(child);
        }
        foreach (var entry in references.Entries) { Resolve(entry.Anchor); foreach (var callee in entry.Callees) ResolveCallee(callee); }
        bool Matches(RuntimeCalleeShape reference, ulong target, IReadOnlyDictionary<string, HashSet<ulong>>? identities = null)
        {
            if (identities is not null && reference.Functions.Any(name => identities.TryGetValue(name, out var expected) && !expected.Contains(target))) return false;
            if (reference.Anchor is { } anchor && resolved[anchor] is { } anchored) return target == anchored;
            if (reference.Shape is null || !ranges.TryGetValue(target, out var range) || range.Length != reference.Length
                || Shape(target) is not { } shape || shape.Text != reference.Shape) return false;
            if (reference.Callees is not { } children) return true;
            return children.Length == shape.Calls.Length
                && children.Select((child, index) => Matches(child, shape.Calls[index], identities)).All(agrees => agrees);
        }
        Parallel.ForEach(image.Functions.Where(r => lengths.Contains(r.Length)),
            new ParallelOptions { MaxDegreeOfParallelism = jobs }, range =>
        {
            if (Shape(range.Start) is not { } shape || !byShape.TryGetValue((range.Length, shape.Text), out var entries)) return;
            foreach (var entry in entries)
            {
                if (entry.Callees.Length != shape.Calls.Length || entry.HasImportCalls != shape.HasImportCalls) continue;
                if (entry.Callees.Length == 0 && !entry.HasImportCalls) continue;
                bool agrees = true;
                for (int i = 0; i < shape.Calls.Length; i++)
                    if (!Matches(entry.Callees[i], shape.Calls[i])) { agrees = false; break; }
                if (agrees) candidatesByReference[entry].Add(new(range.Start, shape));
            }
        });
        var matches = candidatesByReference.ToDictionary(p => p.Key, p => p.Value.OrderBy(c => c.Entry).ToList());
        var contradictions = new Dictionary<string, string>(StringComparer.Ordinal);
        bool Equivalent(List<Candidate> candidates) => candidates.Count > 0 && candidates.Skip(1).All(c =>
            c.Shape is not null && candidates[0].Shape is { } first && c.Shape.Text == first.Text && c.Shape.Calls.SequenceEqual(first.Calls));
        foreach (var (reference, candidates) in matches)
        {
            if (reference.Anchor is not { } anchor || resolved[anchor] is not { } entry) continue;
            if (candidates.Count > 0 && (!candidates.Any(c => c.Entry == entry) || !Equivalent(candidates)))
            {
                contradictions[reference.Function] = "导出锚点与形状匹配入口矛盾";
                candidates.Clear();
            }
            else if (candidates.Count == 0) candidates.Add(new(entry, null));
        }
        var usageProofs = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (reference, candidates) in matches)
        {
            var function = catalog.ByMangledName(reference.Function);
            if (candidates.Count < 2 || Equivalent(candidates) || function.Recognition.UsageConditions.IsEmpty || usageEvidence is null) continue;
            var counts = usageEvidence.Check(function, candidates.Select(c => c.Entry).ToHashSet());
            var proof = "使用处条件：" + string.Join("；", candidates.Select(c =>
                $"0x{c.Entry:x} 满足 {counts[c.Entry].Satisfied}，反例 {counts[c.Entry].Counterexamples}，未核实 {counts[c.Entry].Unverified}，核对 {counts[c.Entry].Checked}/{counts[c.Entry].Total} 调用点"));
            var eligible = candidates.Where(c => counts[c.Entry].Eligible
                && candidates.Where(other => other.Entry != c.Entry).All(other => counts[other.Entry].Satisfied == 0)).ToArray();
            usageProofs[reference.Function] = proof;
            if (eligible.Length == 1)
            {
                candidates.RemoveAll(c => c.Entry != eligible[0].Entry);
            }
            else
            {
                candidates.Clear();
                contradictions[reference.Function] = "使用处条件不能唯一消歧";
            }
        }
        bool changed;
        do
        {
            changed = false;
            // 每轮用同一份身份快照；同义入口的地址集合也是完整身份。
            var identities = matches.Where(p => Equivalent(p.Value)).ToDictionary(p => p.Key.Function,
                p => p.Value.Select(c => c.Entry).ToHashSet(), StringComparer.Ordinal);
            foreach (var (reference, candidates) in matches)
            {
                int removed = candidates.RemoveAll(candidate => candidate.Shape is { } shape
                    && reference.Callees.Select((callee, i) => Matches(callee, shape.Calls[i], identities)).Any(agrees => !agrees));
                if (removed == 0) continue;
                if (reference.Anchor is { } anchor && resolved[anchor] is not null)
                { candidates.Clear(); contradictions[reference.Function] = "导出锚点与目录调用身份矛盾"; }
                else contradictions[reference.Function] = "调用关系与目录函数的唯一入口矛盾";
                changed = true;
            }
        } while (changed);
        IEnumerable<string> CalleeProofs(RuntimeCalleeShape callee)
        {
            if (callee.Anchor is { } anchor && resolved[anchor] is not null) { yield return anchor; yield break; }
            foreach (var child in callee.Callees ?? []) foreach (var proof in CalleeProofs(child)) yield return proof;
        }
        var result = new List<(ulong Entry, RuntimeFunctionLocation Location)>();
        foreach (var (reference, candidates) in matches)
        {
            if (!Equivalent(candidates))
            {
                if (missingReasons is not null)
                    missingReasons[reference.Function] = (contradictions.GetValueOrDefault(reference.Function) ?? (candidates.Count > 1
                        ? $"参考形状与调用关系匹配 {candidates.Count} 个入口，被调目标不同，身份不唯一"
                        : reference.Shape is not null && reference.Callees.Length == 0 && !reference.HasImportCalls
                        ? "形状没有直接调用关系或具名导入印证" : "参考形状或直接调用关系未通过完整复核"))
                        + (reference.Anchor is { } failed && anchorFailures.TryGetValue(failed, out var reason) ? $"；锚点 {failed} 失败：{reason}" : "")
                        + (usageProofs.TryGetValue(reference.Function, out var usage) ? "；" + usage : "");
                continue;
            }
            foreach (var candidate in candidates)
            {
                var anchored = reference.Anchor is { } anchor && resolved[anchor] == candidate.Entry;
                var evidence = anchored ? RuntimeLocationEvidence.ExportAnchor : RuntimeLocationEvidence.ReferenceShape;
                var source = anchored ? reference.Anchor! : "原生 IR 完整形状与直接调用关系";
                if (!anchored)
                {
                    var proofs = reference.Callees.SelectMany(CalleeProofs).Distinct(StringComparer.Ordinal).ToArray();
                    if (proofs.Length > 0) source += "；被调锚点 " + string.Join("，", proofs);
                }
                if (usageProofs.TryGetValue(reference.Function, out var usageProof)) source += "；" + usageProof;
                if (candidates.Count > 1) source += $"；{candidates.Count} 个同形且被调地址相同的同义入口";
                result.Add((candidate.Entry, new(catalog.ByMangledName(reference.Function), evidence, source) { HasEquivalentEntries = candidates.Count > 1 }));
            }
        }
        return result;
    }
}
