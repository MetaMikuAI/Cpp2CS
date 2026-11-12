using System.Diagnostics;
using System.Globalization;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Pipeline;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Recovery.RuntimeFunctions;

namespace Cpp2CS.Tests;

internal static class RuntimeLocateCorpusChecks
{
    public const string Command = "runtime-locate-corpus";
    public static int Run() => Run(true);
    public static int WithoutSymbols() => Run(false);
    private static int Run(bool useSymbols)
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("跳过运行时定位语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var watch = Stopwatch.StartNew();
        // 无符号配置显式清空函数符号证据，真值只在定位结束后读取。
        var image = ElfImage.Load(Path.Combine(corpus, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.so"));
        var spec = RuntimeSpec.Select("2022.3.62f2", "aarch64-linux-android", "LP64");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var (model, registration) = ModelBuilder.Load(image, Path.Combine(corpus, "artifacts/il2cppOutput/data/Metadata/global-metadata.dat"), spec);
        var (map, problems) = RegistrationReader.Read(image, model, spec, registration.CodeRegistration, registration.MetadataRegistration);
        var checks = new Assertions();
        checks.True(problems.Count == 0, "代码地图完整");
        var facts = new GlobalFacts(image, model, map, spec, "arm64") { Symbols = [] };
        if (useSymbols) facts = facts with { Symbols = RecoverySession.CompanionSymbols(image,
            ElfImage.Load(Path.Combine(corpus, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.dbg.so"))) };
        var locateWatch = Stopwatch.StartNew();
        var locations = facts.RuntimeFunctions;
        checks.True(ReferenceEquals(locations, facts.RuntimeFunctions), "每次运行只建立一次");
        if (!useSymbols) checks.True(locations.Entries.Values.SelectMany(e => e.Candidates)
            .All(l => l.Evidence != RuntimeLocationEvidence.Symbol), "无符号定位未使用函数符号证据");
        var locateSeconds = locateWatch.Elapsed.TotalSeconds;
        var errors = 0;
        // 真值只在定位完成后读取，绝不进入定位输入。
        using var functions = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "functions.arm64-v8a.json")));
        var symbols = functions.RootElement.EnumerateArray().GroupBy(f => f.GetProperty("name").GetString()!)
            .ToDictionary(g => g.Key, g => g.ToArray(), StringComparer.Ordinal);
        var synonymous = new HashSet<(ulong Address, string Function)>();
        var truthNames = functions.RootElement.EnumerateArray().Where(f => f.GetProperty("defined").GetBoolean())
            .GroupBy(f => Address(f.GetProperty("address"))).ToDictionary(g => g.Key,
                g => string.Join(" / ", g.Select(f => f.GetProperty("demangled_name").GetString() ?? f.GetProperty("name").GetString()!)));
        foreach (var (address, entry) in locations.Entries.Where(p => p.Value.Selected is not null))
            foreach (var candidate in entry.Candidates)
            {
                var agrees = symbols.TryGetValue(candidate.Function.MangledName, out var definitions)
                    && definitions.Any(d => d.GetProperty("defined").GetBoolean() && Address(d.GetProperty("address")) == address);
                // 同义必须有另一个已定位且符号一致的目录入口作基准；没有基准仍算错误。
                var equivalent = !agrees && candidate.HasEquivalentEntries && definitions is not null && definitions.Any(d =>
                    d.GetProperty("defined").GetBoolean() && locations.Entries.TryGetValue(Address(d.GetProperty("address")), out var canonical)
                    && canonical.Selected is not null && canonical.Candidates.Any(c => c.Function.MangledName == candidate.Function.MangledName && c.HasEquivalentEntries));
                if (equivalent)
                {
                    synonymous.Add((address, candidate.Function.MangledName));
                    Console.WriteLine($"同义入口 | 0x{address:x} | {truthNames.GetValueOrDefault(address) ?? "无符号"} | {candidate.Function.Name} | {candidate.Source} | 待协调者确认");
                }
                if (!agrees && !equivalent) errors++;
                checks.True(agrees || equivalent, $"定位入口 0x{address:x} 与符号逐个一致：{candidate.Function.Name}");
            }
        var missingReasons = new Dictionary<string, int>();
        var independent = 0;
        var found = 0;
        foreach (var function in catalog.Functions)
        {
            var rows = symbols.GetValueOrDefault(function.MangledName) ?? [];
            var defined = rows.Where(r => r.GetProperty("defined").GetBoolean()).ToArray();
            if (defined.Length != 0) independent++;
            var matches = defined.Where(r => locations.Entries.TryGetValue(Address(r.GetProperty("address")), out var entry) && entry.Selected is not null && entry.Candidates.Any(c => c.Function.MangledName == function.MangledName)).ToArray();
            if (matches.Length != 0) found++;
            if (function.Recognition.Import is { } name && locations.Imports.ContainsKey(name))
            {
                var agrees = rows.Any(r => !r.GetProperty("defined").GetBoolean());
                if (!agrees) errors++;
                checks.True(agrees, function.Name + " 导入与真值一致");
                Console.WriteLine($"函数 | {function.Name} | Import | 已定位导入身份 | {(agrees ? "一致" : "错误")}");
            }
            else if (matches.Length != 0)
            {
                checks.True(matches.Length == defined.Length, function.Name + " 符号入口与真值一致");
                var proofs = locations.Entries.Where(p => p.Value.Selected is not null).SelectMany(p => p.Value.Candidates)
                    .Where(c => c.Function.MangledName == function.MangledName).Select(c => $"{c.Evidence}：{c.Source}").Distinct();
                Console.WriteLine($"函数 | {function.Name} | {string.Join("；", proofs)} | 已定位");
            }
            else
            {
                var reason = defined.Length != 0 ? "有独立定义但未定位" :
                    function.Declaration.Split(' ', StringSplitOptions.RemoveEmptyEntries).Contains("inline") ? "内联声明且无独立定义" : "本构建无独立定义";
                missingReasons[reason] = missingReasons.GetValueOrDefault(reason) + 1;
                Console.WriteLine($"函数 | {function.Name} | 未定位 | {reason}；" + locations.Missing.Single(m => m.Function.MangledName == function.MangledName).Reason);
            }
        }
        foreach (var evidence in Enum.GetValues<RuntimeLocationEvidence>())
        {
            var count = locations.Imports.Values.Concat(locations.Entries.Values.Where(e => e.Selected is not null).SelectMany(e => e.Candidates))
                .Where(l => l.Evidence == evidence).Select(l => l.Function.MangledName).Distinct().Count();
            Console.WriteLine($"证据 | {evidence} | {count}");
        }
        foreach (var reason in missingReasons) Console.WriteLine($"未定位分类 | {reason.Key} | {reason.Value}");

        var inline = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_INLINE_TRUTH") ?? truth + "-inline";
        using var audit = JsonDocument.Parse(File.ReadAllText(Path.Combine(inline, "inline-audit.arm64-v8a.json")));
        using var mappings = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "mappings.json")));
        var mapped = mappings.RootElement.EnumerateArray().Where(m => m.GetProperty("method_id").ValueKind != JsonValueKind.Null)
            .SelectMany(m => m.GetProperty("targets").GetProperty("arm64-v8a").EnumerateArray()).ToArray();
        var managed = mapped.Select(m => Address(m.GetProperty("address"))).ToHashSet();
        var managedNames = mapped.Select(m => m.GetProperty("symbol_name").GetString()!).ToHashSet(StringComparer.Ordinal);
        var callers = audit.RootElement.EnumerateArray().Where(a => managed.Contains(Address(a.GetProperty("address"))))
            .GroupBy(a => Address(a.GetProperty("address"))).Select(g => g.First()).ToArray();
        checks.True(callers.Length == managed.Count && callers.Length > 0, "全语料托管地址调用审计完整");
        var calls = callers.SelectMany(a => a.GetProperty("direct_calls").EnumerateArray())
            .GroupBy(c => Address(c.GetProperty("address"))).Select(g => g.First())
            .Where(c => !managed.Contains(Address(c.GetProperty("target"))) &&
                !c.GetProperty("names").EnumerateArray().Any(n => managedNames.Contains(n.GetString()!))).ToArray();
        var covered = 0;
        var exactCovered = 0;
        var synonymCovered = 0;
        foreach (var call in calls)
        {
            var location = locations.Find(Address(call.GetProperty("target")));
            if (location is null) continue;
            covered++;
            var agrees = call.GetProperty("names").EnumerateArray().Any(n => n.GetString() == location.Function.MangledName);
            var equivalent = !agrees && synonymous.Contains((Address(call.GetProperty("target")), location.Function.MangledName));
            if (agrees) exactCovered++;
            else if (equivalent) synonymCovered++;
            else errors++;
            checks.True(agrees || equivalent, $"调用 0x{Address(call.GetProperty("address")):x} 的定位与符号一致");
        }
        var names = catalog.Functions.Select(f => f.MangledName).ToHashSet(StringComparer.Ordinal);
        foreach (var group in calls.GroupBy(c => Address(c.GetProperty("target")))
            .Where(g => !g.Any(c => c.GetProperty("names").EnumerateArray().Any(n => names.Contains(n.GetString()!))))
            .OrderByDescending(g => g.Count()).ThenBy(g => g.Key).Take(20))
        {
            var labels = group.SelectMany(c => c.GetProperty("names").EnumerateArray()).Select(n => n.GetString()!).Distinct()
                .Select(n => symbols.TryGetValue(n, out var rows) ? rows[0].GetProperty("demangled_name").GetString() ?? n : n);
            Console.WriteLine($"目录外 | {string.Join(" / ", labels)} | {group.Count()}");
        }
        foreach (var row in locations.Missing.Select(m => (Missing: m, Calls: calls.Count(c =>
                c.GetProperty("names").EnumerateArray().Any(n => n.GetString() == m.Function.MangledName))))
            .OrderByDescending(r => r.Calls).ThenBy(r => r.Missing.Function.MangledName, StringComparer.Ordinal).Take(20))
            Console.WriteLine($"目录未定位调用 | {row.Calls} | {row.Missing.Function.Name} | {row.Missing.Reason}");
        var missingByName = locations.Missing.ToDictionary(m => m.Function.MangledName, m => m.Reason, StringComparer.Ordinal);
        foreach (var group in calls.GroupBy(c => Address(c.GetProperty("target")))
            .Where(g => locations.Find(g.Key) is null).OrderByDescending(g => g.Count()).ThenBy(g => g.Key).Take(20))
        {
            var targetNames = group.SelectMany(c => c.GetProperty("names").EnumerateArray()).Select(n => n.GetString()!).Distinct().ToArray();
            var labels = targetNames.Select(n => symbols.TryGetValue(n, out var rows) ? rows[0].GetProperty("demangled_name").GetString() ?? n : n);
            var reasons = targetNames.Where(missingByName.ContainsKey).Select(n => missingByName[n]).Distinct().ToArray();
            Console.WriteLine($"未覆盖调用 | {group.Count()} | {string.Join(" / ", labels)} | {(reasons.Length == 0 ? "目录未登记" : string.Join("；", reasons))}");
        }
        checks.True(errors == 0, "定位及调用点与真值核对错误数为零");
        if (useSymbols) checks.True(found == independent, "全部具有独立定义的目录函数已定位");
        checks.True(covered > 0, "定位覆盖非空");
        if (!useSymbols) checks.True(found > 0, "无符号依据定位了具有独立定义的运行时目录函数");
        Console.WriteLine($"同义入口 {synonymous.Count}；符号一致调用覆盖 {exactCovered}；同义调用覆盖 {synonymCovered}（待协调者确认）");
        Console.WriteLine($"独立定义定位 {found}/{independent}；系统导入 {locations.Imports.Count}；加权覆盖 {covered}/{calls.Length} ({(double)covered / calls.Length:P2})；错误数 {errors}；定位含不返回分析 {locateSeconds:F2}s；核对总计 {watch.Elapsed.TotalSeconds:F2}s");
        return checks.Finish("运行时定位 ARM64 真值核对");
    }
    private static ulong Address(JsonElement value) => ulong.Parse(value.GetString()!.Replace("0x", "", StringComparison.Ordinal), NumberStyles.HexNumber, CultureInfo.InvariantCulture);
}

internal static class RuntimeLocateWithoutSymbolsCorpusChecks
{
    public const string Command = "runtime-locate-nosymbols-corpus";
    public static int Run() => RuntimeLocateCorpusChecks.WithoutSymbols();
}
