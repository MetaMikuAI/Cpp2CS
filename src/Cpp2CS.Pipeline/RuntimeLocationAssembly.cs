using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime;
using Cpp2CS.Native;
using Cpp2CS.Targets.Arm64;
using System.Diagnostics;
using Cpp2CS.Targets.Frontend;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

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

    /// <summary>逐项写出定位结果：定位到的入口与依据，没定位到的函数与原因。只在已经定位过时写。</summary>
    internal static void Write(GlobalFacts facts, string path)
    {
        if (!locations.TryGetValue(facts, out var value) || !value.IsValueCreated) return;
        var result = value.Value.Value;
        var document = new
        {
            imports = result.Imports.OrderBy(e => e.Key, StringComparer.Ordinal).Select(e => new { import = e.Key, function = e.Value.Function.Name }),
            entries = result.Entries.OrderBy(e => e.Key).Select(e => new
            {
                entry = $"0x{e.Key:x}", function = e.Value.Selected?.Function.Name, evidence = e.Value.Selected?.Evidence.ToString(),
                source = e.Value.Selected?.Source, reason = e.Value.Reason,
                candidates = e.Value.Candidates.Select(c => c.Function.Name).Distinct(StringComparer.Ordinal),
            }),
            missing = result.Missing.OrderBy(m => m.Function.Name, StringComparer.Ordinal).Select(m => new { function = m.Function.Name, reason = m.Reason }),
        };
        File.WriteAllText(path, System.Text.Json.JsonSerializer.Serialize(document, new System.Text.Json.JsonSerializerOptions
        { WriteIndented = true, Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping }));
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
        IEnumerable<RuntimeManagedCaller> ManagedCallers(IReadOnlySet<ulong> candidates)
        {
            foreach (var entry in facts.CodeMap.Entries.Where(e => e.Method is not null).Select(e => e.Address).Distinct().Order())
            {
                var ranges = facts.FunctionsByStart[entry].ToArray();
                if (ranges.Length != 1) throw new InvalidDataException("托管入口没有唯一函数范围，无法普查调用点。");
                var sites = Arm64DirectCalls.ToCandidates(facts.Image, ranges[0], candidates).ToArray();
                if (sites.Length == 0) continue;
                yield return new(entry, sites.GroupBy(s => s.Target).ToDictionary(g => g.Key, g => g.Count()), () => Read());
                IEnumerable<RuntimeManagedUse> Read()
                {
                    var body = ranges[0].HasConsistentExtent ? FunctionLifter.Lift(referenceInstructions, parts.Convention,
                        parts.Flow, ranges[0], entry).Function : null;
                    var calls = body?.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Trace is not null)
                        .ToDictionary(c => c.Trace!.NativeAddress);
                    foreach (var site in sites)
                    {
                        var call = calls?.GetValueOrDefault(site.Address);
                        if (call is not null && Normalize(call.Target) != new ImageFunction(site.Target)) call = null;
                        yield return new(site.Target, body, call);
                    }
                }
            }
        }
        RuntimeUsageEvidence? usage = null;
        if (references is not null && facts.Architecture == "arm64")
        {
            var pointer = facts.Image.PointerWidth;
            var binder = new MethodBinder(new(new FieldLayouts(facts.Spec, pointer, pointer), pointer * 8), new Aapcs64());
            usage = new(facts.Image, binder, new RuntimeMetadataSlotValidator(facts), ManagedCallers, RecoverySession.AnalysisJobs(facts));
        }
        if (references is not null)
        {
            if (references.Entries.Length > 0)
                matches = RuntimeShapeMatcher.Locate(facts.Image, catalog, references, entry =>
                {
                    var ranges = facts.FunctionsByStart[entry].ToArray();
                    return ranges.Length != 1 ? null : FunctionLifter.Lift(referenceInstructions, parts.Convention,
                        parts.Flow, ranges[0], entry).Function;
                }, Normalize, missingReasons, RecoverySession.AnalysisJobs(facts), usage);
        }
        return RuntimeFunctionLocations.Locate(facts.Image, facts.Symbols, catalog, Normalize, matches, missingReasons);
    }
}
