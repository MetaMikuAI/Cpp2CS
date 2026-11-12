using System.Collections.Immutable;
using System.Globalization;
using System.IO.Compression;
using System.Numerics;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Targets.Frontend;
using static Cpp2CS.Targets.Arm64.Arm64Registers;

namespace Cpp2CS.Tests;

internal static class Arm64Checks
{
    public const string Command = "arm64";
    internal static string EvidenceDirectory
    {
        get
        {
            var directory = new DirectoryInfo(AppContext.BaseDirectory);
            while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "Cpp2CS.slnx"))) directory = directory.Parent;
            return Path.Combine(directory?.FullName ?? throw new InvalidOperationException("找不到源码根目录。"), "tests", "Cpp2CS.Tests", "Arm64Evidence");
        }
    }
    public static int Run()
    {
        var checks = new Assertions();
        Slots(checks);
        Integration(checks);
        var model = new Arm64InstructionSet(new InputMemoryImage());
        var state = new Concrete(); var exception = state.Terms.Constant(7, 64); var selector = state.Terms.Constant(3, 64);
        model.EnterHandler(state, exception, selector);
        checks.True(state.Read(X[0]) == exception && state.Read(X[1]) == selector,
            "异常模型按 AArch64 落地约定提供异常对象与选择值");
        checks.True(model.IsResumeUnwind(new ImportedTarget(new("_Unwind_Resume"))) && model.ResumeException(state) == exception
            && !model.IsResumeUnwind(new ImportedTarget(new("__cxa_end_catch"))),
            "异常模型只按导入身份识别继续展开");
        using var input = File.OpenRead(Path.Combine(EvidenceDirectory, "evidence.json.gz"));
        checks.True(input.Length <= 2 * 1024 * 1024, "压缩证据不超过 2 MiB");
        using var compressed = new GZipStream(input, CompressionMode.Decompress);
        using var document = JsonDocument.Parse(compressed);
        var root = document.RootElement;
        checks.True(root.GetProperty("generator_sha256").GetString() == Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(Path.Combine(EvidenceDirectory, "generate.py")))), "生成器校验和匹配");
        checks.True(root.GetProperty("capstone").GetString() == "5.0.7" && root.GetProperty("unicorn").GetString() == "2.1.4", "证据工具版本固定");
        foreach (var group in root.GetProperty("cases").EnumerateArray().GroupBy(c => c.GetProperty("group").GetString()).OrderBy(g => g.Key, StringComparer.Ordinal))
        {
            int mismatches = 0;
            foreach (var item in group)
            {
                var emitter = new Concrete(item);
                Arm64InstructionSet.DecodeWord(Concrete.Pc, item.GetProperty("word").GetUInt32()).Instruction!.Emit(emitter);
                var problems = emitter.Problems(item);
                if (problems.Count != 0)
                {
                    mismatches++;
                    if (mismatches <= 3) Console.Error.WriteLine($"{group.Key} {item.GetProperty("word").GetUInt32():x8} {item.GetProperty("mnemonic").GetString()}: {string.Join(';', problems)}");
                }
            }
            Console.WriteLine($"取证 {group.Key}: 用例={group.Count()} 不一致={mismatches}");
            checks.True(mismatches == 0, $"{group.Key} 与独立模拟器一致");
        }
        RejectUnsupported(checks);
        return checks.Finish("ARM64 前端");
    }
    private static void Slots(Assertions checks)
    {
        var classifier = new Aapcs64();
        CType[] types = [new CInteger(8), new CInteger(16), new CInteger(32), new CInteger(64), new CInteger(128), new CPointer(64), new CFloat(32), new CFloat(64),
            .. Enumerable.Range(1, 4).Select(n => new CAggregate(n * 8, 8, [.. Enumerable.Range(0, n).Select(i => new CField(i * 8, new CFloat(64)))])),
            new CAggregate(24, 8, [new(0, new CInteger(64)), new(8, new CInteger(64)), new(16, new CInteger(64))])];
        var arguments = new HashSet<AbstractSlot>(); var results = new HashSet<AbstractSlot>();
        foreach (var type in types)
        {
            var assignment = classifier.Classify(new([.. Enumerable.Repeat(type, 10)], type)).Assignment!;
            foreach (var value in assignment.Parameters)
            {
                foreach (var piece in value.Pieces) if (piece.Slot.Kind != SlotKind.ArgumentArea) arguments.Add(piece.Slot);
                if (value.CopyAddress is { Slot.Kind: not SlotKind.ArgumentArea } copy) arguments.Add(copy.Slot);
            }
            if (assignment.Return.BufferAddress is { } address) arguments.Add(address.Slot);
            foreach (var piece in assignment.Return.Pieces) results.Add(piece.Slot);
        }
        checks.True(arguments.SetEquals(Convention.Arguments.Select(s => s.Slot)), "分类器实参寄存器槽与约定双向相等");
        checks.True(results.SetEquals(Convention.Results.Select(s => s.Slot)), "分类器结果寄存器槽与约定双向相等");
        checks.True(All.Distinct().Count() == All.Length && Convention.Arguments.All(s => All.Contains(s.Register)), "单元唯一且槽位均在寄存器文件中");
        checks.True(Convention.PreservedParts.All(p => p.Width == 64 && p.Low == 0 && !Convention.Preserved.Contains(p.Register) && Convention.CallerValues.Contains(p.Register)), "部分保存有调用方身份且不冒充全单元保存");
        checks.True(Convention.CallerValues.Contains(X[30]) && !Convention.Preserved.Contains(X[30]), "返回地址有入口身份且跨调用破坏");
    }
    private sealed class Words(uint[] code) : IInstructionSet
    {
        public ImmutableArray<Register> Registers => All;
        public DecodeResult Decode(ulong address) => address % 4 == 0 && address / 4 < (ulong)code.Length
            ? Arm64InstructionSet.DecodeWord(address, code[address / 4])
            : new(null, new("test.fetch", "测试指令越界。"));
    }
    private static void Integration(Assertions checks)
    {
        foreach (var code in new uint[][]
        {
            [0x91000400, 0xd65f03c0],
            [0xa9bf7bfd, 0x910003fd, 0x94000100, 0xa8c17bfd, 0xd65f03c0],
            [0x7100001f, 0x54000060, 0x52800020, 0x14000002, 0x52800040, 0xd65f03c0],
            [0x14000100],
            [0x5400200e],
            [0x5400200f]
        })
        {
            LiftResult Lift() => FunctionLifter.Lift(new Words(code), Convention, new Arm64FlowFacts(), new(0, (ulong)code.Length * 4, FunctionEvidence.SymbolTable), 0);
            var first = Lift();
            checks.True(first.Function is not null && first.Failure is null, "整数、序言恢复、条件分支与直接尾调用接入共用驱动：" + first.Failure);
            if (first.Function is not null)
            {
                checks.True(ExitChecker.Check(first.Function).IsValid, "ARM64 产物通过出口");
                checks.True(TextDump.Write(first.Function, true) == TextDump.Write(Lift().Function!, true), "重复提升保持稳定转储");
            }
        }
        var indirect = FunctionLifter.Lift(new Words([0xd61f0000]), Convention, new Arm64FlowFacts(), new(0, 4, FunctionEvidence.SymbolTable), 0);
        checks.True(indirect.Function is { } tail && tail.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(c => c.Target is ComputedTarget),
            "栈指针已复位时经寄存器的跳转是尾调用");
    }
    private static void RejectUnsupported(Assertions checks)
    {
        foreach (var (word, code) in new (uint, string)[] { (0x1ee02820, "floating"), (0x1e264020, "floating"), (0x1e240020, "floating"), (0x0e217820, "vector"),
            (0xd53b4400, "system-register"), (0xd53b4420, "system-register"), (0xd51b4420, "system-register"), (0xd51b4400, "system-register"),
            (0xd5033bbf, "barrier"), (0xd5033f5f, "exclusive"), (0x4c408120, "vector"), (0x4d40d920, "vector"), (0x4d40dd20, "vector"), (0x885f7c00, "exclusive"), (0xb8200000, "atomic"), (0x00000000, "unallocated") })
        {
            var emitter = new Concrete();
            Arm64InstructionSet.DecodeWord(Concrete.Pc, word).Instruction!.Emit(emitter);
            checks.True(emitter.Failure?.Code == "arm64." + code, "未支持编码按类别报洞：" + code);
        }
    }
    internal sealed class Concrete : IEmitter
    {
        internal const ulong Pc = 0x100000;
        public TermTable Terms { get; } = new();
        private readonly Dictionary<Register, Term> state = [];
        private readonly Queue<(ulong Address, byte Value)> reads = new();
        private readonly List<(ulong Address, byte Value)> actualReads = [], writes = [];
        private ulong next = Pc + 4;
        private bool trap;
        private readonly List<string> errors = [];
        public Reason? Failure { get; private set; }
        public Concrete() { foreach (var r in All) state[r] = Terms.Constant(0, r.Width); }
        public Concrete(JsonElement item)
        {
            var before = item.GetProperty("before").EnumerateArray().ToArray();
            for (int i = 0; i < All.Length; i++) state[All[i]] = Terms.Constant(Parse(before[i]), All[i].Width);
            foreach (var access in item.GetProperty("accesses").EnumerateArray().Where(a => a[0].GetString() == "read"))
                foreach (var value in Bytes(access)) reads.Enqueue(value);
        }
        private static BigInteger Parse(JsonElement element) => BigInteger.Parse(element.GetString()!, CultureInfo.InvariantCulture);
        private static IEnumerable<(ulong Address, byte Value)> Bytes(JsonElement access)
        {
            ulong address = ulong.Parse(access[1].GetString()!, CultureInfo.InvariantCulture); var value = Parse(access[3]);
            for (int i = 0; i < access[2].GetInt32() / 8; i++) yield return (address + (ulong)i, (byte)((value >> (8 * i)) & 255));
        }
        private BigInteger Value(Term term)
        {
            if (term.ConstantValue is { } constant) return constant;
            var evaluated = new TermEvaluator(_ => throw new InvalidOperationException("具体发射器不应有原子。")).Evaluate(term);
            if (evaluated.Status != EvaluationStatus.Defined) { errors.Add("非具体项：" + evaluated.Status); return 0; }
            return evaluated.Bits;
        }
        public Term Read(Register register) => state[register];
        public void Write(Register register, Term value)
        {
            if (value.Width != register.Width) errors.Add("非整单元写入");
            state[register] = value;
        }
        public Term Load(Term address, int width)
        {
            ulong pointer = (ulong)Value(address); BigInteger result = 0;
            for (int i = 0; i < width / 8; i++)
            {
                if (!reads.TryDequeue(out var expected)) { errors.Add("额外读取"); continue; }
                if (expected.Address != pointer + (ulong)i) errors.Add("读取地址不一致");
                actualReads.Add((pointer + (ulong)i, expected.Value)); result |= (BigInteger)expected.Value << (8 * i);
            }
            return Terms.Constant(result, width);
        }
        public void Store(Term address, Term value)
        {
            ulong pointer = (ulong)Value(address); var bits = Value(value);
            for (int i = 0; i < value.Width / 8; i++) writes.Add((pointer + (ulong)i, (byte)((bits >> (i * 8)) & 255)));
        }
        public void Call(CallTarget target) => next = target switch { ImageFunction f => f.EntryOffset, ComputedTarget t => (ulong)Value(t.Value), _ => throw new InvalidOperationException() };
        public void Jump(ulong target) => next = target;
        public void Branch(Term condition, ulong whenTrue, ulong whenFalse) => next = Value(condition).IsZero ? whenFalse : whenTrue;
        public void IndirectJump(Term target) => next = (ulong)Value(target);
        public void Return() => next = (ulong)Value(Read(X[30]));
        public void Trap() { trap = true; next = Pc; }
        public void TrapIf(Term condition) { if (!Value(condition).IsZero) Trap(); }
        public Term ImageAddress(ulong offset) => Terms.Constant(offset, 64);
        public Term ThreadPointer => Terms.Constant(0x201230, 64);
        public void Fail(Reason reason) => Failure = reason;
        private static bool IsNaN(BigInteger value, int width)
        {
            int fraction = width == 32 ? 23 : 52, exponent = width == 32 ? 8 : 11;
            var mask = (BigInteger.One << fraction) - 1;
            return ((value >> fraction) & ((1 << exponent) - 1)) == (1 << exponent) - 1 && (value & mask) != 0;
        }
        public List<string> Problems(JsonElement item)
        {
            if (Failure is not null) errors.Add(Failure.ToString());
            var after = item.GetProperty("after").EnumerateArray().ToArray();
            int floatWidth = item.TryGetProperty("float_result", out var format) ? format.GetInt32() : 0;
            int destination = (int)(item.GetProperty("word").GetUInt32() & 31) + 32;
            for (int i = 0; i < All.Length; i++)
            {
                var actual = Value(state[All[i]]); var expected = Parse(after[i]);
                var comparable = actual;
                if (floatWidth != 0 && i == destination)
                {
                    int lanes = item.GetProperty("float_lanes").GetInt32(), low = item.GetProperty("float_low").GetInt32();
                    var mask = (BigInteger.One << floatWidth) - 1;
                    for (int lane = 0; lane < lanes; lane++)
                    {
                        int shift = low + lane * floatWidth;
                        if (IsNaN(actual >> shift, floatWidth) && IsNaN(expected >> shift, floatWidth))
                            comparable = (comparable & ~(mask << shift)) | (expected & (mask << shift));
                    }
                }
                if (comparable != expected) errors.Add($"{All[i].Name} expected={expected:x} actual={actual:x}");
            }
            if (next != item.GetProperty("next").GetUInt64()) errors.Add($"PC expected={item.GetProperty("next")} actual={next}");
            if (trap != item.GetProperty("trap").GetBoolean()) errors.Add("陷阱不一致");
            if (reads.Count != 0) errors.Add("遗漏读取");
            var expectedWrites = item.GetProperty("accesses").EnumerateArray().Where(a => a[0].GetString() == "write").SelectMany(Bytes);
            if (!writes.SequenceEqual(expectedWrites)) errors.Add("内存写入不一致");
            return errors;
        }
    }
}
