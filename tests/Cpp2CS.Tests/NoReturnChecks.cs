using System.Collections.Immutable;
using System.Collections.Concurrent;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Targets.Frontend;
using Cpp2CS.Targets.Arm64;

namespace Cpp2CS.Tests;

internal static class NoReturnChecks
{
    public const string Command = "noreturn";
    private static readonly Register Value = new("value", 64), Sp = new("stack", 64), Flag = new("flag", 1);
    private static readonly RegisterConvention Convention = new([], [], [], Sp, 0, 0, []);
    private sealed class Toy(Dictionary<ulong, Action<IEmitter>> code) : IInstructionSet, INoReturnInstructionSet
    {
        public bool IsStraightLineFailure(Cpp2CS.Native.Terms.Reason reason) => reason.Code == "toy.straight";
        public CallTarget ResolveCallTarget(IImage image, CallTarget target) => target is ImageFunction { EntryOffset: 900 } ? new ImportedTarget(new ImportSymbol("toy_import")) : target;
        public ImmutableArray<Register> Registers => [Value, Sp, Flag];
        public ConcurrentDictionary<ulong, int> Decodes { get; } = new();
        public DecodeResult Decode(ulong address)
        {
            Decodes.AddOrUpdate(address, 1, (_, count) => count + 1);
            return code.TryGetValue(address, out var emit)
                ? new(new(1, emit), null) : new(null, new("toy.missing", "缺指令"));
        }
    }
    public static int Run()
    {
        var checks = new Assertions();
        var import = new ImportSymbol("toy_import");
        var isa = new Toy(new()
        {
            [0] = e => e.Call(new ImportedTarget(import)),
            [10] = e => e.Call(new ImageFunction(0)),
            [11] = e => e.Return(),
            [20] = e => e.Branch(e.Read(Flag), 21, 22),
            [21] = e => e.Return(), [22] = e => e.Call(new ImageFunction(0)),
            [30] = e => e.IndirectJump(e.Read(Value)),
            [40] = e => e.Call(new ImageFunction(50)), [50] = e => e.Call(new ImageFunction(40)),
            [60] = e => e.Jump(0), [70] = e => e.Jump(11), [80] = e => e.Jump(80),
            [90] = e => e.Fail(new("toy.straight", "未支持的直线指令")), [91] = e => e.Call(new ImportedTarget(import)),
            [100] = e => e.Fail(new("toy.unknown", "控制流未知")), [101] = e => e.Call(new ImportedTarget(import)),
            [110] = e => e.Branch(e.Read(Flag), 111, 112),
            [111] = e => e.Call(new ImageFunction(900)), [112] = e => e.Return(),
            [200] = e => e.Write(Value, e.Read(Value)), [201] = e => e.Call(new ImageFunction(0)), [202] = e => e.Return()
        });
        FunctionRange Range(ulong start, ulong length = 1) => new(start, length, FunctionEvidence.UnwindTable);
        var ranges = new[] { Range(0), Range(10), Range(11), Range(20, 3), Range(30), Range(40), Range(50), Range(60), Range(70), Range(80), Range(90, 2), Range(100, 2), Range(110, 3), Range(200, 3) };
        // 玩具指令不读取映像，空映像只承载入口参数。
        var facts = NoReturnAnalysis.Analyze(new InputMemoryImage(), isa, Convention, ranges, [import], new Arm64FlowFacts());
        foreach (ulong entry in new ulong[] { 0, 10, 60, 80, 90, 200, 900 }) checks.True(facts.DoesNotReturn(new ImageFunction(entry)), $"证明 {entry}");
        foreach (ulong entry in new ulong[] { 11, 20, 30, 40, 50, 70, 100, 110 }) checks.True(!facts.DoesNotReturn(new ImageFunction(entry)), $"保守拒绝 {entry}");
        checks.True(FunctionLifter.Lift(isa, Convention, facts, Range(10), 10).Function is not null, "截断调用后的其他函数代码并通过提升");
        checks.True(FunctionLifter.Lift(isa, Convention, facts, Range(90, 2), 90).Failure?.Reason.Code == "toy.straight", "正常提升仍拒绝未支持指令");
        checks.True(facts.Rounds >= 2, "调用者经迭代发现");
        checks.True(isa.Decodes[200] == 1, "不依赖已知集合的指令只解码一次");
        checks.True(isa.Decodes[201] == 2, "调用答案变化后重新发射");
        checks.True(isa.Decodes[202] == 1, "证明不返回后不再探测调用后继");
        var parallel = NoReturnAnalysis.Analyze(new InputMemoryImage(), isa, Convention, ranges.Reverse(), [import], new Arm64FlowFacts(), jobs: 4);
        checks.True(facts.Targets.SetEquals(parallel.Targets), "线程数和输入范围顺序不影响目标集合");
        checks.True(facts.Rounds == parallel.Rounds, "线程数和输入范围顺序不影响轮数");
        return checks.Finish("不返回分析");
    }
}
