using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime;
using Cpp2CS.Native;
using Cpp2CS.Targets.Arm64;
using System.Diagnostics;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Pipeline;

/// <summary>与默认前端共用一次创建的组件；恢复层不引用目标实现。</summary>
internal static class RuntimeLocationAssembly
{
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<FrontendComponents>> components = [];
    internal static FrontendComponents Components(GlobalFacts facts, Func<GlobalFacts, FrontendComponents> create) =>
        components.GetValue(facts, f => new(() => create(f))).Value;

    private sealed record Located(RuntimeFunctionLocations Value, double Seconds);
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<Located>> locations = [];
    internal static RuntimeFunctionLocations Locations(GlobalFacts facts) => locations.GetValue(facts, f => new(() =>
    {
        var watch = Stopwatch.StartNew();
        var value = Locate(f);
        return new Located(value, watch.Elapsed.TotalSeconds);
    })).Value.Value;
    internal static double Seconds(GlobalFacts facts) => locations.TryGetValue(facts, out var value) && value.IsValueCreated ? value.Value.Seconds : 0;
    internal static Dictionary<string, int> Evidence(GlobalFacts facts)
    {
        if (!locations.TryGetValue(facts, out var value) || !value.IsValueCreated) return [];
        var result = value.Value.Value;
        return result.Imports.Values.Concat(result.Entries.Values.Where(e => e.Selected is not null).SelectMany(e => e.Candidates))
            .GroupBy(e => e.Evidence.ToString()).ToDictionary(g => g.Key, g => g.Select(e => e.Function.MangledName).Distinct().Count());
    }

    private static RuntimeFunctionLocations Locate(GlobalFacts facts)
    {
        var catalog = RuntimeFunctionCatalog.Select(facts.Spec.Layout.UnityVersion, facts.Spec.Layout.Triple, facts.Spec.Layout.DataModel);
        var parts = RecoverySession.DefaultComponents(facts);
        CallTarget Normalize(CallTarget target) => parts.Instructions is INoReturnInstructionSet resolver
            ? resolver.ResolveCallTarget(facts.Image, target) : target;
        var referenceInstructions = facts.Architecture == "arm64" ? new Arm64InstructionSet(facts.Image, orderedMemory: true) : parts.Instructions;
        var references = facts.Symbols.IsEmpty ? RuntimeShapeCatalog.Select(catalog.UnityVersion, catalog.Triple, catalog.DataModel) : null;
        IReadOnlyList<(ulong Entry, RuntimeFunctionLocation Location)> matches = [];
        var missingReasons = new Dictionary<string, string>(StringComparer.Ordinal);
        if (facts.Symbols.IsEmpty)
            foreach (var function in catalog.Functions.Where(f => f.Recognition.Import is null))
                missingReasons[function.MangledName] = references is null ? "没有匹配版本与目标的参考形状数据"
                    : "参考形状缺失：" + (references.Missing.FirstOrDefault(m => m.Function == function.MangledName)?.Reason ?? "参考构建未提供完整形状");
        if (references is not null)
        {
            if (references.Entries.Length > 0)
                matches = RuntimeShapeMatcher.Locate(facts.Image, catalog, references, entry =>
                {
                    var ranges = facts.FunctionsByStart[entry].ToArray();
                    return ranges.Length != 1 ? null : FunctionLifter.Lift(referenceInstructions, parts.Convention,
                        parts.Flow, ranges[0], entry).Function;
                }, Normalize, missingReasons, RecoverySession.AnalysisJobs(facts));
        }
        return RuntimeFunctionLocations.Locate(facts.Image, facts.Symbols, catalog, Normalize, matches, missingReasons);
    }
}
