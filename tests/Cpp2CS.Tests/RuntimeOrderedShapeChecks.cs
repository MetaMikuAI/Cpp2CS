using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class RuntimeOrderedShapeChecks
{
    public const string Command = "runtime-ordered-shapes";
    private sealed class Instructions(uint[] words, bool ordered) : IInstructionSet
    {
        public ImmutableArray<Register> Registers => Arm64Registers.All;
        public DecodeResult Decode(ulong address) => Arm64InstructionSet.DecodeWord(address, words[checked((int)(address / 4))], ordered);
    }
    private static LiftResult Lift(uint[] words, bool ordered = true) => FunctionLifter.Lift(new Instructions(words, ordered),
        Arm64Registers.Convention, new Arm64FlowFacts(), new FunctionRange(0, (ulong)words.Length * 4, FunctionEvidence.UnwindTable), 0);
    public static int Run()
    {
        var checks = new Assertions();
        for (int size = 0; size < 4; size++)
        {
            // Arm DDI0602：无偏移的 acquire/release 访问；基址为第一个入口槽，数据为第二个槽。
            var words = new uint[] { 0x08dffc01u | ((uint)size << 30), 0x089ffc01u | ((uint)size << 30), 0xd5033bbf, 0xd65f03c0 };
            var lifted = Lift(words);
            checks.True(lifted.Function is not null, "参考分析完整保留有序访问");
            if (lifted.Function is not { } function) continue;
            var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
            var read = statements.OfType<MemoryRead>().Single();
            var write = statements.OfType<MemoryWrite>().Single();
            checks.True(read.Acquire && write.Release && read.Width == 8 << size && write.Width == read.Width,
                "访问宽度与单向顺序语义保留");
            checks.True(ReferenceEquals(read.Result, write.Value), "读取值原样写回，不丢失窄位型");
            checks.True(statements.OfType<MemoryFence>().Single() is { Domain: "inner-shareable", Ordering: FenceOrdering.ReadWrite },
                "全读写屏障域与访问种类保留");
            var text = RuntimeReferenceShape.Create(function, t => t)!.Text;
            checks.True(text.Contains(" acquire") && text.Contains(" release") && text.Contains("fence "), "参考形状包含同步语义");
            checks.True(Lift(words, false).Failure?.Reason.Code == "arm64.exclusive", "普通恢复未启用同步词汇时仍报洞");
        }
        var shapes = new List<string>();
        for (int domain = 0; domain < 4; domain++)
            for (int access = 1; access <= 3; access++)
            {
                var words = new uint[] { 0xd50330bfu | ((uint)domain << 10) | ((uint)access << 8), 0xd65f03c0 };
                var function = Lift(words).Function!;
                var fence = function.Blocks.SelectMany(b => b.Statements).OfType<MemoryFence>().Single();
                checks.True(fence.Ordering == (access switch { 1 => FenceOrdering.Read, 2 => FenceOrdering.Write, _ => FenceOrdering.ReadWrite }),
                    "DMB 的读到读写、写到写与读写到读写分别保留");
                shapes.Add(RuntimeReferenceShape.Create(function, t => t)!.Text);
                checks.True(Lift(words, false).Failure?.Reason.Code == "arm64.barrier", "普通恢复不启用任何 DMB 形式");
            }
        checks.True(shapes.Distinct().Count() == 12, "不同观察域与访问种类不产生相同形状");
        checks.True(Lift([0xd5033b9f, 0xd65f03c0]).Failure?.Reason.Code == "arm64.barrier", "等待完成屏障不能冒充观察顺序屏障");
        checks.True(Lift([0xd50338bf, 0xd65f03c0]).Failure?.Reason.Code == "arm64.barrier", "未支持的保留选项仍报洞");
        var terms = new Cpp2CS.Native.Terms.TermTable(); var entry = new BlockIdentity();
        var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        builder.Blocks.Add(new(entry, [], [new MemoryFence(new(), "system") { Ordering = (FenceOrdering)99 }], new Return([])));
        checks.True(ExitChecker.Check(builder.Freeze()).Violations.Any(v => v.Code == "fence-ordering"), "出口检查拒绝非法屏障顺序");
        ExclusiveChecks(checks);
        return checks.Finish("参考形状同步语义");
    }
    private static void ExclusiveChecks(Assertions checks)
    {
        var shapes = new List<string>();
        for (int size = 0; size < 4; size++)
        foreach (bool ordered in new[] { false, true })
        {
            // LDXR/LDAXR、STXR/STLXR、CBNZ 写状态回到读、CLREX、RET。
            uint order = ordered ? 0x8000u : 0;
            var words = new uint[] { 0x085f7c02u | ((uint)size << 30) | order,
                0x08037c01u | ((uint)size << 30) | order, 0x35ffffc3, 0xd5033f5f, 0xd65f03c0 };
            var result = Lift(words, false);
            checks.True(result.Function is not null, "独占读写与重试状态提升：" + result.Failure);
            if (result.Function is not { } function) continue;
            var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
            var read = statements.OfType<ExclusiveRead>().Single(); var write = statements.OfType<ExclusiveWrite>().Single();
            checks.True(read.Address == write.Address && read.Width == 8 << size && write.Width == read.Width
                && read.Acquire == ordered && write.Release == ordered && write.Status.Width == 32, "独占对保留地址、宽度、顺序与状态结果");
            checks.True(statements.OfType<ExclusiveClear>().Count() == 1 && ExitChecker.Check(function).IsValid, "清除监视器进入事件并通过出口检查");
            checks.True(function.Blocks.Where(b => b.End is Branch).Select(b => ((Branch)b.End).Condition)
                .Any(condition => SnapshotRewrite.Dependencies([condition]).Contains(write.Status)), "失败分支使用独占写的状态寄存器结果");
            var shape = RuntimeReferenceShape.Create(function, t => t)!.Text; shapes.Add(shape);
            checks.True(shape.Contains("exclusive-read") && shape.Contains("exclusive-write") && shape.Contains("exclusive-clear"), "完整形状可引用独占对");
            var noBackEdge = (uint[])words.Clone(); noBackEdge[2] = 0xd503201f;
            checks.True(RuntimeReferenceShape.Create(Lift(noBackEdge).Function!, t => t)!.Text != shape, "没有失败重试回边不是同一形状");
            checks.True(RuntimeReferenceShape.Create(new SnapshotRewrite(function).Apply(), t => t)!.Text == shape, "快照重写保留独占身份与结果");
        }
        checks.True(shapes.Distinct().Count() == 8, "不同宽度与访问顺序不能同形");
        checks.True(Lift([0xc87f8440, 0xd65f03c0]).Failure?.Reason.Code == "arm64.exclusive", "成对独占访问保留缺口");
        checks.True(Lift([0xc81f7c1f, 0xd65f03c0]).Failure?.Reason.Code == "arm64.constrained-unpredictable", "独占写状态与数据重叠不能提供确定事件");
        checks.True(Lift([0xb8200000, 0xd65f03c0]).Failure?.Reason.Code == "arm64.atomic", "LSE 访问保留缺口");
    }

}
