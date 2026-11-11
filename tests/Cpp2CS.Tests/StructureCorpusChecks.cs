using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class StructureCorpusChecks
{
    public const string Command = "structure-corpus";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS"); var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(root) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("跳过结构语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var checks = new Assertions();
        var artifact = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts");
        Directory.CreateDirectory(artifact);
        var caseOutput = Path.Combine(artifact, "structure-cases.local.output");
        Directory.CreateDirectory(caseOutput);
        using var detail = new StreamWriter(Path.Combine(artifact, "structure-corpus.local.jsonl"));
        var image = ElfImage.Load(Path.Combine(root, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.so"));
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model, registration) = ModelBuilder.Load(image, Path.Combine(root, "artifacts/il2cppOutput/data/Metadata/global-metadata.dat"), spec);
        var (map, problems) = RegistrationReader.Read(image, model, spec, registration.CodeRegistration, registration.MetadataRegistration);
        checks.True(problems.Count == 0, "代码地图完整");
        var facts = new GlobalFacts(image, model, map, spec, "arm64") { Symbols = RecoverySession.CompanionSymbols(image,
            ElfImage.Load(Path.Combine(root, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.dbg.so"))) };
        var layouts = new FieldLayouts(spec, image.PointerWidth, image.PointerWidth);
        var binder = new MethodBinder(new(layouts, image.PointerWidth * 8), new Aapcs64());
        var types = new ManagedTypes(model, layouts, image.PointerWidth);
        using var cases = InputCorpusChecks.Json(truth, "cases.json");
        var selected = cases.RootElement.EnumerateArray().ToDictionary(r => r.GetProperty("mapping").GetProperty("metadata_method_id").GetString()!,
            r => r.GetProperty("case").GetProperty("method").GetString()!);
        var isa = new Arm64InstructionSet(image); var flow = NoReturnCorpusChecks.Analyze(image);
        var removed = new Dictionary<string, int>(); var rejected = new Dictionary<string, (int Count, string Example)>();
        var before = new Dictionary<string, int>(); var after = new Dictionary<string, int>();
        var timings = new Dictionary<string, double>();
        var structureTime = new System.Diagnostics.Stopwatch();
        int changed = 0, branches = 0, total = 0, contracts = 0, listed = 0, assumptions = 0;
        void Count(Dictionary<string, int> counts, string key) => counts[key] = counts.GetValueOrDefault(key) + 1;
        foreach (var group in map.Entries.Where(e => e.Method is not null).GroupBy(e => e.Method!.Method))
        {
            var entry = group.OrderBy(e => e.Kind).ThenBy(e => e.Address).ThenBy(e => e.Index).First();
            var id = RecoverySession.Identity(group.Key); total++;
            var range = facts.FunctionsByStart[entry.Address].SingleOrDefault();
            var lifted = range is null ? null : FunctionLifter.Lift(isa, Arm64Registers.Convention, flow, range, entry.Address);
            if (lifted?.Function is not { } function)
            {
                var why = lifted?.Failure?.Reason.Code ?? "frontend.function_range"; Count(before, why); Count(after, why);
                if (selected.TryGetValue(id, out var failed)) { Console.WriteLine($"用例 {failed}：提升失败 {why}"); listed++; }
                continue;
            }
            var kind = entry.Kind switch { EntryKind.Method => BindingEntryKind.Ordinary, EntryKind.GenericMethod => BindingEntryKind.SharedGeneric,
                EntryKind.AdjustorThunk or EntryKind.GenericAdjustorThunk => BindingEntryKind.AdjustorThunk,
                EntryKind.Invoker => BindingEntryKind.Invoker, _ => BindingEntryKind.Wrapper };
            var original = new IntegerLowering(function, MethodRef.Open(group.Key), binder, types, image).Run(kind);
            Count(before, original.Body is not null ? "complete" : original.Failure!.Reason.Code);
            var methodStart = structureTime.Elapsed.TotalSeconds;
            structureTime.Start();
            var transformed = StructureRecovery.Run(function, new(group.Key, entry, facts), binder, kind, layouts);
            structureTime.Stop();
            detail.WriteLine(System.Text.Json.JsonSerializer.Serialize(new { id, Elapsed = structureTime.Elapsed.TotalSeconds - methodStart, transformed.Timings, Records = transformed.Records }));
            foreach (var (key, seconds) in transformed.Timings) timings[key] = timings.GetValueOrDefault(key) + seconds;
            if (!ReferenceEquals(function, transformed.Function)) changed++;
            if (!transformed.Assumptions.IsEmpty) assumptions++;
            if (!ExitChecker.Check(transformed.Function).IsValid) contracts++;
            foreach (var record in transformed.Records)
            {
                if (record.Removed)
                { if (record.Kind == "branch") branches++; else Count(removed, record.Kind + ":" + record.Evidence); }
                else
                {
                    var key = record.Kind + ":" + record.Evidence;
                    var old = rejected.GetValueOrDefault(key); rejected[key] = (old.Count + 1, old.Example ?? $"{id}@0x{record.Address:x}");
                }
            }
            var recovered = new IntegerLowering(transformed.Function, MethodRef.Open(group.Key), binder, types, image).Run(kind);
            Count(after, recovered.Body is not null ? "complete" : recovered.Failure!.Reason.Code);
            if (selected.TryGetValue(id, out var label))
            {
                File.WriteAllText(Path.Combine(caseOutput, label + ".local.txt"), TextDump.Write(transformed.Function, true));
                Console.WriteLine($"剩余 {label}：分支={transformed.Function.Blocks.Count(b => b.End is Branch)} 合流={transformed.Function.Blocks.Sum(b => b.Merges.Length)} "
                    + string.Join(" ", transformed.Function.Blocks.SelectMany(b => b.Statements).GroupBy(s => s.GetType().Name).Select(g => $"{g.Key}={g.Count()}"))
                    + $" 下降={recovered.Failure?.Reason.Code ?? "complete"}");
                listed++; Console.WriteLine($"用例 {label}：" + string.Join("；", transformed.Records.Select(r => $"{(r.Removed ? "消去" : "保留")} {r.Kind}@0x{r.Address:x} {r.Evidence}")));
            }
            if (total % 2000 == 0) Console.WriteLine($"结构进度={total} 改变={changed}");
        }
        Console.WriteLine($"结构耗时={structureTime.Elapsed.TotalSeconds:F3}s " + string.Join(" ", timings.Select(p => $"{p.Key}={p.Value:F3}s")));
        Console.WriteLine($"结构总计：方法={total} 改变={changed} 折叠分支={branches} 使用未定义值假设的方法={assumptions}");
        foreach (var (key, count) in removed.OrderByDescending(p => p.Value)) Console.WriteLine($"删除 {key}={count}");
        foreach (var (key, value) in rejected.OrderByDescending(p => p.Value.Count)) Console.WriteLine($"保留 {key}={value.Count} 例={value.Example}");
        foreach (var (key, count) in before.OrderByDescending(p => p.Value)) Console.WriteLine($"接入前 {key}={count}");
        foreach (var (key, count) in after.OrderByDescending(p => p.Value)) Console.WriteLine($"接入后 {key}={count}");
        checks.True(contracts == 0, "所有输出通过原生出口检查"); checks.True(listed == selected.Count, "全部用例逐个列出");
        return checks.Finish("结构定向检查");
    }
}
