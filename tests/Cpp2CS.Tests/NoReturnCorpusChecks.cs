using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
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
        var rounds = new List<NoReturnRound>();
        var facts = Analyze(image, observe: rounds.Add);
        Console.WriteLine($"不返回目标={facts.Targets.Count} 映像入口={facts.Targets.OfType<ImageFunction>().Count()} 轮数={facts.Rounds} 毫秒={watch.Elapsed.TotalMilliseconds:F0}");
        foreach (var round in rounds)
            Console.WriteLine($"noreturn_round={round.Number} pending={round.Pending} added={round.Added} seconds={round.Elapsed.TotalSeconds:F6}");
        var probes = rounds.SelectMany(r => r.Probes).Select(t => t.TotalMilliseconds).Order().ToArray();
        Console.WriteLine($"noreturn_probes={probes.Length} p50_ms={probes[probes.Length / 2]:F6} p95_ms={probes[probes.Length * 95 / 100]:F6} p99_ms={probes[probes.Length * 99 / 100]:F6} max_ms={probes[^1]:F6}");
        // 参照为逐轮重新解码、发射的原算法：全部目标按 ToString 序数排序，以换行连接后取 UTF-8 的 SHA-256。
        // 摘要覆盖导入与映像入口的完整集合；语料变更时须用参照算法重新核对，不能只更新数量。
        var canonical = string.Join("\n", facts.Targets.Select(t => t.ToString()).Order(StringComparer.Ordinal));
        var digest = Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(canonical)));
        Console.WriteLine($"noreturn_digest count={facts.Targets.Count} sha256={digest}");
        checks.True(digest == "609547926C3D2C83271536091492280B919646554631A75B0CC96A442194451A", "不返回目标集合与原算法摘要逐项一致");
        watch.Restart();
        var serial = Analyze(image, jobs: 1);
        Console.WriteLine($"noreturn_serial_seconds={watch.Elapsed.TotalSeconds:F6}");
        checks.True(facts.Targets.SetEquals(serial.Targets), "单线程与并行的不返回目标逐个相同");
        checks.True(facts.Rounds == serial.Rounds, "单线程与并行的不返回轮数相同");
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
    internal static NoReturnFacts Analyze(IImage image, int? jobs = null, Action<NoReturnRound>? observe = null)
    {
        var catalog = RuntimeCatalogChecks.Load(RuntimeCatalogChecks.Paths().Single(p => p.EndsWith("-arm64.json", StringComparison.Ordinal)));
        var names = catalog.Functions.Where(f => f.Recognition.Import is not null && f.Operation.DoesNotReturn)
            .Select(f => f.Recognition.Import!).ToHashSet(StringComparer.Ordinal);
        return NoReturnAnalysis.Analyze(image, new Arm64InstructionSet(image), Arm64Registers.Convention, image.Functions,
            image.Imports.Where(i => names.Contains(i.Name)), new Arm64FlowFacts(), jobs: jobs ?? Environment.ProcessorCount, observe: observe);
    }

}
