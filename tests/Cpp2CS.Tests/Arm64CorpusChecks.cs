using System.Diagnostics;
using System.Globalization;
using System.Text.Json;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class Arm64CorpusChecks
{
    public const string Command = "arm64-corpus";
    private sealed record Row(ulong Address, ulong Length, string? Failure, ulong? FailureAddress);
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("跳过 ARM64 语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var checks = new Assertions();
        var image = ElfImage.Load(Path.Combine(corpus, "artifacts", "il2cppOutput", "build", "arm64-v8a", "libil2cpp.so"));
        var noReturnFile = Directory.EnumerateFiles(truth, "*.json").Where(f => Path.GetFileName(f).Contains("noreturn", StringComparison.OrdinalIgnoreCase)
            || Path.GetFileName(f).Contains("non-return", StringComparison.OrdinalIgnoreCase)).SingleOrDefault();
        var noReturns = new HashSet<ulong>();
        if (noReturnFile is not null)
        {
            using var known = JsonDocument.Parse(File.ReadAllText(noReturnFile));
            foreach (var entry in known.RootElement.EnumerateArray()) noReturns.Add(Address(entry.ValueKind == JsonValueKind.Object ? entry.GetProperty("address") : entry) - image.PreferredBase);
            Console.WriteLine($"不返回清单：读取 {noReturns.Count} 个入口。");
        }
        else Console.WriteLine("不返回清单：无；全部调用按返回处理，可能继续发现到函数范围之外。");
        var facts = new Arm64FlowFacts(t => t is ImageFunction f && noReturns.Contains(f.EntryOffset));
        var isa = new Arm64InstructionSet(image);
        List<Row>? previous = null;
        var unsupported = new Dictionary<(string Category, uint Word), long>();
        var categoryInstructions = new Dictionary<string, long>();
        var exclusiveCategories = new Dictionary<string, int>();
        long totalInstructions = 0;
        for (int run = 0; run < 2; run++)
        {
            var rows = new List<Row>(); var watch = Stopwatch.StartNew();
            foreach (var range in image.Functions.OrderBy(f => f.Start))
            {
                var result = FunctionLifter.Lift(isa, Arm64Registers.Convention, facts, range, range.Start);
                checks.True((result.Function is null) != (result.Failure is null), "函数必须是完整产物或带原因的洞");
                if (result.Function is { } function) checks.True(ExitChecker.Check(function).IsValid, "提升成功的函数通过出口检查");
                rows.Add(new(range.Start, range.Length, result.Failure?.Reason.Code, result.Failure?.Address));
                if (rows.Count % 2000 == 0) Console.WriteLine($"提升进度 {run + 1}: {rows.Count}/{image.Functions.Length}");
            }
            watch.Stop();
            if (run == 0)
            {
                previous = rows;
                foreach (var range in image.Functions)
                {
                    var probe = new Probe(); var categories = new HashSet<string>();
                    for (ulong offset = 0; offset + 4 <= range.Length; offset += 4)
                    {
                        totalInstructions++;
                        var decoded = isa.Decode(range.Start + offset); probe.Failure = decoded.Failure;
                        decoded.Instruction?.Emit(probe);
                        if (probe.Failure is not { } failure) continue;
                        categories.Add(failure.Code);
                        categoryInstructions[failure.Code] = categoryInstructions.GetValueOrDefault(failure.Code) + 1;
                        if (image.IsExecutable(range.Start + offset, 4))
                        {
                            var key = (failure.Code, (uint)image.ReadUnsigned(range.Start + offset, 4));
                            unsupported[key] = unsupported.GetValueOrDefault(key) + 1;
                        }
                    }
                    if (categories.Count == 1)
                    { var category = categories.Single(); exclusiveCategories[category] = exclusiveCategories.GetValueOrDefault(category) + 1; }
                }
            }
            else checks.True(previous!.SequenceEqual(rows), "两次运行每个函数的结果与洞位置完全一致");
            int good = rows.Count(r => r.Failure is null);
            Console.WriteLine($"语料运行 {run + 1}: 函数={rows.Count} 通过={good} 占比={(double)good / rows.Count:P6} 指令={totalInstructions} 时间毫秒={watch.Elapsed.TotalMilliseconds:F3} 纳秒每指令={watch.Elapsed.TotalNanoseconds / totalInstructions:F3}");
            if (run != 0) continue;
            foreach (var group in rows.Where(r => r.Failure is not null).GroupBy(r => r.Failure).OrderByDescending(g => g.Count()).ThenBy(g => g.Key, StringComparer.Ordinal).Take(20))
                Console.WriteLine($"函数洞 {group.Key}: {group.Count()}");
            foreach (var pair in categoryInstructions.OrderByDescending(p => p.Value).ThenBy(p => p.Key, StringComparer.Ordinal).Take(20)) Console.WriteLine($"指令洞 {pair.Key}: {pair.Value}");
            foreach (var pair in exclusiveCategories.OrderBy(p => p.Key, StringComparer.Ordinal)) Console.WriteLine($"仅含一种编码缺口 {pair.Key}: {pair.Value}（仍可能受控制流或栈检查阻挡）");
        }
        using var cases = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "cases.json")));
        foreach (var item in cases.RootElement.EnumerateArray())
        {
            var name = item.GetProperty("case").GetProperty("method").GetString();
            var targets = item.GetProperty("mapping").GetProperty("targets").GetProperty("arm64-v8a");
            foreach (var target in targets.EnumerateArray())
            {
                ulong address = Address(target.GetProperty("address")) - image.PreferredBase;
                var row = previous!.SingleOrDefault(r => r.Address == address);
                checks.True(row is not null, "真值函数入口包含在映像函数表中");
                Console.WriteLine($"用例 {name}: {(row is null ? "缺函数范围" : row.Failure ?? "通过")}");
            }
        }
        // 外部助记符报告器只接收编码和类别，不携带业务名称或地址。
        string? output = Environment.GetEnvironmentVariable("CPP2CS_ARM64_HISTOGRAM");
        if (!string.IsNullOrEmpty(output)) File.WriteAllText(output, JsonSerializer.Serialize(unsupported.OrderBy(p => p.Key.Category, StringComparer.Ordinal).ThenBy(p => p.Key.Word)
            .Select(p => new { category = p.Key.Category, word = p.Key.Word, count = p.Value })));
        Console.WriteLine("汇总 SHA256=" + Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(JsonSerializer.SerializeToUtf8Bytes(previous))));
        return checks.Finish("ARM64 全语料");
    }
    private static ulong Address(JsonElement value) => value.ValueKind == JsonValueKind.Number ? value.GetUInt64() : ulong.Parse(value.GetString()!.AsSpan(2), NumberStyles.HexNumber, CultureInfo.InvariantCulture);
    private sealed class Probe : IEmitter
    {
        public TermTable Terms { get; } = new();
        public Reason? Failure { get; set; }
        public Term Read(Register register) => Terms.Constant(0, register.Width);
        public void Write(Register register, Term value) { }
        public Term Load(Term address, int width) => Terms.Constant(0, width);
        public void Store(Term address, Term value) { }
        public void Call(CallTarget target) { }
        public void Jump(ulong target) { }
        public void Branch(Term condition, ulong whenTrue, ulong whenFalse) { }
        public void IndirectJump(Term target) { }
        public void Return() { }
        public void Trap() { }
        public void TrapIf(Term condition) { }
        public Term ImageAddress(ulong offset) => Terms.Constant(offset, 64);
        public Term ThreadPointer => Terms.Constant(0, 64);
        public void Fail(Reason reason) => Failure = reason;
    }
}
