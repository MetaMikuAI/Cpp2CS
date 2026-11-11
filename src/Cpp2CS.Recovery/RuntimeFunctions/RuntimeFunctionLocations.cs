using System.Collections.Frozen;
using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.RuntimeFunctions;

public enum RuntimeLocationEvidence { Import, Symbol }
public sealed record RuntimeFunctionLocation(RuntimeFunction Function, RuntimeLocationEvidence Evidence, string Source);
public sealed record RuntimeLocationMissing(RuntimeFunction Function, string Reason);
/// <summary>保留同址的全部目录身份；操作相同时按修饰名排序取首项，否则不定位并记录原因。</summary>
public sealed record RuntimeEntryLocation(ImmutableArray<RuntimeFunctionLocation> Candidates, RuntimeFunctionLocation? Selected, string? Reason);

/// <summary>映像提供身份依据；目标归一由装配处提供，包含目标平台的 PLT 解析。查询不改变事实。</summary>
public sealed class RuntimeFunctionLocations
{
    private readonly Func<CallTarget, CallTarget> normalize;
    private RuntimeFunctionLocations(FrozenDictionary<string, RuntimeFunctionLocation> imports,
        FrozenDictionary<ulong, RuntimeEntryLocation> entries,
        ImmutableArray<RuntimeLocationMissing> missing, Func<CallTarget, CallTarget> normalize)
    { Imports = imports; Entries = entries; Missing = missing; this.normalize = normalize; }

    public FrozenDictionary<string, RuntimeFunctionLocation> Imports { get; }
    public FrozenDictionary<ulong, RuntimeEntryLocation> Entries { get; }
    public ImmutableArray<RuntimeLocationMissing> Missing { get; }

    public RuntimeFunctionLocation? Find(ulong entry) => Find(new ImageFunction(entry));
    public RuntimeFunctionLocation? Find(CallTarget target) => normalize(target) switch
    {
        ImportedTarget import => Imports.GetValueOrDefault(import.Symbol.Name),
        ImageFunction function => Entries.GetValueOrDefault(function.EntryOffset)?.Selected,
        _ => null
    };

    public static RuntimeFunctionLocations Locate(IImage image, RuntimeFunctionCatalog catalog,
        Func<CallTarget, CallTarget> normalize) => Locate(image, image.FunctionSymbols, catalog, normalize);

    /// <summary>函数符号由调用方给出：映像自己的符号表，或同一次构建的伴随文件；可以为空。</summary>
    public static RuntimeFunctionLocations Locate(IImage image, ImmutableArray<FunctionSymbol> symbols, RuntimeFunctionCatalog catalog,
        Func<CallTarget, CallTarget> normalize)
    {
        var imports = new Dictionary<string, RuntimeFunctionLocation>(StringComparer.Ordinal);
        var present = image.Imports.Select(i => i.Name).ToHashSet(StringComparer.Ordinal);
        foreach (var group in catalog.Functions.Where(f => f.Recognition.Import is not null)
            .GroupBy(f => f.Recognition.Import!, StringComparer.Ordinal))
            if (group.Count() == 1 && present.Contains(group.Key))
                imports.Add(group.Key, new(group.Single(), RuntimeLocationEvidence.Import, group.Key));

        var byName = catalog.Functions.Where(f => f.Recognition.Symbol).ToDictionary(f => f.MangledName, StringComparer.Ordinal);
        var entries = symbols.Where(s => byName.ContainsKey(s.Name)).GroupBy(s => s.Offset)
            .ToFrozenDictionary(g => g.Key, g =>
            {
                var candidates = g.Select(s => s.Name).Distinct().Order(StringComparer.Ordinal)
                    .Select(n => new RuntimeFunctionLocation(byName[n], RuntimeLocationEvidence.Symbol, n)).ToImmutableArray();
                var agrees = candidates.Select(c => c.Function.Operation).Distinct().Count() == 1;
                return new RuntimeEntryLocation(candidates, agrees ? candidates[0] : null,
                    agrees ? (candidates.Length > 1 ? "同址别名操作相同，按修饰名取首项" : null) : "同址别名对应不同运行时操作");
            });
        var located = imports.Values.Select(l => l.Function.MangledName).Concat(entries.Values.Where(e => e.Selected is not null)
            .SelectMany(e => e.Candidates).Select(c => c.Function.MangledName)).ToHashSet(StringComparer.Ordinal);
        var conflicts = entries.Values.Where(e => e.Selected is null).SelectMany(e => e.Candidates)
            .Select(c => c.Function.MangledName).ToHashSet(StringComparer.Ordinal);
        var missing = catalog.Functions.Where(f => !located.Contains(f.MangledName)).Select(f => new RuntimeLocationMissing(f,
            conflicts.Contains(f.MangledName) ? "同址别名对应不同运行时操作" :
            f.Recognition.Import is not null ? "映像没有唯一匹配的导入" :
            !f.Recognition.Symbol ? "目录未启用符号证据" :
            symbols.IsEmpty ? "没有函数符号证据" : "符号表没有该函数的独立定义")).ToImmutableArray();
        return new(imports.ToFrozenDictionary(StringComparer.Ordinal), entries, missing, normalize);
    }
}
