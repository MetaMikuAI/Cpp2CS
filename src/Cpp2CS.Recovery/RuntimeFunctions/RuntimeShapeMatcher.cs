using System.Collections.Concurrent;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.RuntimeFunctions;

/// <summary>范围长度仅用于候选筛选；完整形状及全部直接被调形状均相同且入口唯一才采纳。并行时提升与归一化须可并发查询。</summary>
public static class RuntimeShapeMatcher
{
    private sealed record Candidate(ulong Entry, ulong[] Calls);
    public static IReadOnlyList<(ulong Entry, RuntimeFunctionLocation Location)> Locate(IImage image,
        RuntimeFunctionCatalog catalog, RuntimeShapeCatalog references, Func<ulong, NativeFunction?> lift,
        Func<CallTarget, CallTarget> normalize, IDictionary<string, string>? missingReasons = null, int jobs = 1)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(jobs, 1);
        var handlers = new TryRegionIndex(image.TryRegions);
        var ranges = image.Functions.ToDictionary(f => f.Start);
        var lengths = references.Entries.Select(e => e.Length).ToHashSet();
        var byShape = references.Entries.GroupBy(e => (e.Length, e.Shape)).ToDictionary(g => g.Key, g => g.ToArray());
        var candidatesByReference = references.Entries.ToDictionary(e => e, _ => new ConcurrentBag<Candidate>());
        // 仅缓存被调摘要，避免持有全映像的项表与快照。
        var callees = new ConcurrentDictionary<ulong, Lazy<RuntimeReferenceShape?>>();
        RuntimeReferenceShape? Callee(ulong entry) => callees.GetOrAdd(entry, key => new(() =>
        {
            if (!ranges.TryGetValue(key, out var range) || !range.HasConsistentExtent || handlers.HasHandlerInRange(range.Start, range.Length)) return null;
            var function = lift(key);
            return function is null ? null : RuntimeReferenceShape.Create(function, normalize, image);
        })).Value;
        bool Matches(RuntimeCalleeShape reference, ulong target, IReadOnlyDictionary<string, ulong>? unique = null)
        {
            if (unique is not null && reference.Functions.Any(name => unique.TryGetValue(name, out var expected) && expected != target)) return false;
            if (!ranges.TryGetValue(target, out var range) || range.Length != reference.Length
                || Callee(target) is not { } shape || shape.Text != reference.Shape) return false;
            if (reference.Callees is not { } children) return true;
            return children.Length == shape.Calls.Length
                && children.Select((child, index) => Matches(child, shape.Calls[index], unique)).All(agrees => agrees);
        }
        Parallel.ForEach(image.Functions.Where(r => lengths.Contains(r.Length)),
            new ParallelOptions { MaxDegreeOfParallelism = jobs }, range =>
        {
            if (!range.HasConsistentExtent || handlers.HasHandlerInRange(range.Start, range.Length)) return;
            var function = lift(range.Start);
            var shape = function is null ? null : RuntimeReferenceShape.Create(function, normalize, image);
            if (shape is null || !byShape.TryGetValue((range.Length, shape.Text), out var entries)) return;
            foreach (var entry in entries)
            {
                if (entry.Callees.Length != shape.Calls.Length || entry.HasImportCalls != shape.HasImportCalls) continue;
                if (entry.Callees.Length == 0 && !entry.HasImportCalls) continue;
                bool agrees = true;
                for (int i = 0; i < shape.Calls.Length; i++)
                    if (!Matches(entry.Callees[i], shape.Calls[i])) { agrees = false; break; }
                if (agrees) candidatesByReference[entry].Add(new(range.Start, shape.Calls));
            }
        });
        var matches = candidatesByReference.ToDictionary(p => p.Key, p => p.Value.OrderBy(c => c.Entry).ToList());
        var contradictions = new HashSet<string>(StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            // 每轮使用同一份唯一入口快照，不能因枚举顺序选择冲突的一方。
            var unique = matches.Where(p => p.Value.Count == 1).ToDictionary(p => p.Key.Function, p => p.Value[0].Entry, StringComparer.Ordinal);
            foreach (var (reference, candidates) in matches)
            {
                int removed = candidates.RemoveAll(candidate => reference.Callees.Select((callee, i) => Matches(callee, candidate.Calls[i], unique))
                    .Any(agrees => !agrees));
                if (removed == 0) continue;
                contradictions.Add(reference.Function); changed = true;
            }
        } while (changed);
        foreach (var (reference, candidates) in matches)
            if (candidates.Count != 1 && missingReasons is not null)
                missingReasons[reference.Function] = reference.Callees.Length == 0 && !reference.HasImportCalls
                    ? "形状没有直接调用关系或具名导入印证" : candidates.Count == 0
                    ? contradictions.Contains(reference.Function) ? "调用关系与目录函数的唯一入口矛盾" : "参考形状或直接调用关系未通过完整复核"
                    : $"参考形状与调用关系匹配 {candidates.Count} 个入口，身份不唯一";
        return matches.Where(p => p.Value.Count == 1).Select(p => (p.Value[0].Entry, new RuntimeFunctionLocation(
            catalog.ByMangledName(p.Key.Function), RuntimeLocationEvidence.ReferenceShape, p.Key.Callees.Length == 0 ? "原生 IR 唯一形状与具名导入调用" : $"原生 IR 唯一形状与 {p.Key.Callees.Length} 个直接被调形状及补充关系"))).ToArray();
    }
}
