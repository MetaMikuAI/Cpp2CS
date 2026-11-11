using System.Diagnostics;
using System.Globalization;
using System.Text.Json;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class NoReturnCorpusChecks
{
    public const string Command = "noreturn-corpus";
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("跳过不返回语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var checks = new Assertions();
        var binary = Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a");
        var image = ElfImage.Load(Path.Combine(binary, "libil2cpp.so"));
        var isa = new Arm64InstructionSet(image);
        var catalog = RuntimeCatalogChecks.Load(RuntimeCatalogChecks.Paths().Single(p => p.EndsWith("-arm64.json", StringComparison.Ordinal)));
        var watch = Stopwatch.StartNew();
        var facts = Analyze(image);
        Console.WriteLine($"不返回目标={facts.Targets.Count} 映像入口={facts.Targets.OfType<ImageFunction>().Count()} 轮数={facts.Rounds} 毫秒={watch.Elapsed.TotalMilliseconds:F0}");
        using var symbols = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "functions.arm64-v8a.json")));
        foreach (var function in catalog.Functions.Where(f => f.Recognition.Import is null && f.Operation.DoesNotReturn))
            foreach (var symbol in symbols.RootElement.EnumerateArray().Where(s => s.GetProperty("name").GetString() == function.MangledName && s.GetProperty("defined").GetBoolean()))
            {
                var entry = ulong.Parse(symbol.GetProperty("address").GetString()!.AsSpan(2), NumberStyles.HexNumber, CultureInfo.InvariantCulture) - image.PreferredBase;
                checks.True(facts.DoesNotReturn(new ImageFunction(entry)), $"运行时不返回核对 {function.Name} 0x{entry:x}");
                Console.WriteLine($"目录核对 {function.Name} 0x{entry:x}: {facts.DoesNotReturn(new ImageFunction(entry))}");
            }
        var results = new Dictionary<ulong, (LiftFailure? Before, LiftFailure? After)>();
        foreach (var range in image.Functions.OrderBy(r => r.Start))
        {
            var before = FunctionLifter.Lift(isa, Arm64Registers.Convention, new Arm64FlowFacts(), range, range.Start);
            var after = FunctionLifter.Lift(isa, Arm64Registers.Convention, facts, range, range.Start);
            results.Add(range.Start, (before.Failure, after.Failure));
            if (after.Function is { } function) checks.True(ExitChecker.Check(function) is { IsValid: true, Holes.IsEmpty: true }, "出口检查");
            if (results.Count % 2000 == 0) Console.WriteLine($"进度 {results.Count}/{image.Functions.Length}");
        }
        for (int stage = 0; stage < 2; stage++)
        {
            var rows = results.Select(p => (p.Key, Failure: stage == 0 ? p.Value.Before : p.Value.After)).ToArray();
            Console.WriteLine($"{(stage == 0 ? "前" : "后")} 通过={rows.Count(r => r.Failure is null)}/{rows.Length}");
            foreach (var group in rows.Where(r => r.Failure is not null).GroupBy(r => r.Failure!.Reason.Code).OrderByDescending(g => g.Count()))
                Console.WriteLine($"洞 {group.Key}={group.Count()}");
        }
        foreach (var row in results.Where(p => p.Value.After?.Reason.Code == "fallthrough-range"))
            Console.WriteLine($"剩余落空 入口=0x{row.Key:x} 指令=0x{row.Value.After!.Address:x}");
        using var cases = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "cases.json")));
        foreach (var item in cases.RootElement.EnumerateArray())
            foreach (var target in item.GetProperty("mapping").GetProperty("targets").GetProperty("arm64-v8a").EnumerateArray())
            {
                var address = ulong.Parse(target.GetProperty("address").GetString()!.AsSpan(2), NumberStyles.HexNumber, CultureInfo.InvariantCulture) - image.PreferredBase;
                var row = results[address];
                Console.WriteLine($"用例 {item.GetProperty("case").GetProperty("method").GetString()}: {row.Before?.Reason.Code ?? "通过"} -> {row.After?.Reason.Code ?? "通过"}");
            }
        return checks.Finish("不返回语料");
    }
    internal static NoReturnFacts Analyze(IImage image)
    {
        var catalog = RuntimeCatalogChecks.Load(RuntimeCatalogChecks.Paths().Single(p => p.EndsWith("-arm64.json", StringComparison.Ordinal)));
        var names = catalog.Functions.Where(f => f.Recognition.Import is not null && f.Operation.DoesNotReturn)
            .Select(f => f.Recognition.Import!).ToHashSet(StringComparer.Ordinal);
        return NoReturnAnalysis.Analyze(image, new Arm64InstructionSet(image), Arm64Registers.Convention, image.Functions,
            image.Imports.Where(i => names.Contains(i.Name)), new Arm64FlowFacts());
    }

}
