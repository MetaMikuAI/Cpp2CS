using System.Globalization;
using System.Text.Json;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class IndirectCorpusChecks
{
    public const string Command = "indirect-corpus";
    private sealed class Facts(IFlowFacts inner, bool baseline) : IFlowFacts
    {
        internal readonly Dictionary<ulong, IndirectResolution> Resolutions = [];
        internal readonly Dictionary<ulong, string> Evidence = [];
        public bool DoesNotReturn(CallTarget target) => inner.DoesNotReturn(target);
        public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context)
        {
            var result = baseline ? new IndirectUnknown(new("arm64.indirect", "经寄存器的跳转目标无法判定。"))
                : inner.ResolveIndirect(address, target, context);
            Resolutions[address] = result;
            if (!baseline && result is IndirectUnknown)
                Evidence[address] = Describe(target, context, 0) + " 条件=" + string.Join(";", context.Conditions.Select(c => c.IsTrue + ":" + Describe(c.Condition, context, 0)));

            return result;
        }
    }
    private static string Describe(Term t, IIndirectContext context, int depth)
    {
        if (depth > 24) return "…";
        if (context.InUniquePredecessor(t) is { } previous) return Describe(previous, context, depth + 1);
        if (context.ReadOf(t) is { } read) return $"read{read.Width}[{Describe(read.Address, context, depth + 1)}]";
        if (t.ConstantValue is { } value) return $"{value:x}:{t.Width}";
        if (t.Identity is { } atom) return atom.StableText + ":" + t.Width;
        return $"{t.Operator?.Name ?? t.Kind.ToString()}:{t.Width}:{t.SliceLow}(" + string.Join(",", t.Operands.Select(o => Describe(o, context, depth + 1))) + ")";
    }
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("跳过间接跳转语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var checks = new Assertions();
        var image = ElfImage.Load(Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a", "libil2cpp.so"));
        var isa = new Arm64InstructionSet(image);
        var inner = NoReturnCorpusChecks.Analyze(image);
        using var symbols = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "functions.arm64-v8a.json")));
        var extents = symbols.RootElement.EnumerateArray().Where(s => s.GetProperty("defined").GetBoolean() && s.GetProperty("size").GetUInt64() != 0)
            .Select(s => (Start: Address(s.GetProperty("address")) - image.PreferredBase, Size: s.GetProperty("size").GetUInt64(), Name: s.GetProperty("name").GetString()))
            .GroupBy(s => s.Start).ToDictionary(g => g.Key, g => g.ToArray());
        var before = new Dictionary<ulong, LiftFailure?>(); var after = new Dictionary<ulong, LiftFailure?>();
        int tables = 0, tails = 0;
        var evidence = new Dictionary<string, string>();
        foreach (var range in image.Functions.OrderBy(r => r.Start))
        {
            before.Add(range.Start, FunctionLifter.Lift(isa, Arm64Registers.Convention, new Facts(inner, true), range, range.Start).Failure);
            var facts = new Facts(inner, false);
            var result = FunctionLifter.Lift(isa, Arm64Registers.Convention, facts, range, range.Start);
            after.Add(range.Start, result.Failure);
            if (result.Failure is { } failure && facts.Evidence.TryGetValue(failure.Address, out var detail))
                evidence.TryAdd(failure.Reason.Code, $"0x{range.Start:x}/0x{failure.Address:x} " + detail);
            if (result.Function is { } function) checks.True(ExitChecker.Check(function) is { IsValid: true, Holes.IsEmpty: true }, "出口检查");
            foreach (var resolution in facts.Resolutions.Values)
            {
                if (resolution is IndirectTailCall) tails++;
                if (resolution is not IndirectTable table) continue;
                tables++;
                var targets = table.Cases.Select(c => c.Target).Append(table.Default).ToArray();
                checks.True(extents.TryGetValue(range.Start, out var matches) && matches.Any(s => targets.All(t => t >= s.Start && t - s.Start < s.Size)), "表的所有目标属于同一个符号函数范围");
            }
            if (after.Count % 2000 == 0) Console.WriteLine($"间接跳转进度 {after.Count}/{image.Functions.Length}");
        }
        foreach (var (label, rows) in new[] { ("前", before), ("后", after) })
        {
            Console.WriteLine($"{label} 通过={rows.Count(r => r.Value is null)}/{rows.Count}");
            foreach (var group in rows.Where(r => r.Value is not null).GroupBy(r => r.Value!.Reason.Code).OrderByDescending(g => g.Count()))
            {
                var example = group.First();
                Console.WriteLine($"洞 {group.Key}={group.Count()} 例=0x{example.Key:x}/0x{example.Value!.Address:x} {example.Value.Reason.Message}");
            }
        }
        foreach (var pair in evidence) Console.WriteLine($"间接洞证据 {pair.Key}: {pair.Value}");
        Console.WriteLine($"解析跳转表={tables} 尾调用={tails}（每函数每跳转位置的最终解析，含随后报洞的函数）");
        using var cases = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "cases.json")));
        foreach (var item in cases.RootElement.EnumerateArray())
            foreach (var target in item.GetProperty("mapping").GetProperty("targets").GetProperty("arm64-v8a").EnumerateArray())
            {
                var address = Address(target.GetProperty("address")) - image.PreferredBase;
                Console.WriteLine($"用例 {item.GetProperty("case").GetProperty("method").GetString()}: {before[address]?.Reason.Code ?? "通过"} -> {after[address]?.Reason.Code ?? "通过"}");
            }
        return checks.Finish("间接跳转语料");
    }
    private static ulong Address(JsonElement value) => value.ValueKind == JsonValueKind.Number ? value.GetUInt64()
        : ulong.Parse(value.GetString()!.AsSpan(2), NumberStyles.HexNumber, CultureInfo.InvariantCulture);
}
