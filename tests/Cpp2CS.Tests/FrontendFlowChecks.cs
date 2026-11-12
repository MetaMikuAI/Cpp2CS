using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class FrontendFlowChecks
{
    public const string Command = "frontend-flow";
    public static int Run()
    {
        var checks = new Assertions();
        Patch(checks);
        Calls(checks);
        return checks.Finish("前端链接器控制流");
    }
    private static uint B(ulong source, ulong target, bool link = false) =>
        (link ? 0x94000000u : 0x14000000u) | ((uint)(unchecked((long)(target - source)) >> 2) & 0x03ffffff);
    private static LiftResult Lift(InputMemoryImage image, FunctionRange range) =>
        FunctionLifter.Lift(new Arm64InstructionSet(image), Arm64Registers.Convention, new Arm64FlowFacts(), range, range.Start);
    private static void Patch(Assertions checks)
    {
        var range = new FunctionRange(0, 16, FunctionEvidence.UnwindTable);
        var image = new InputMemoryImage { Executable = true, Functions = [range] };
        image.Put(0, 0xd10043ff, 4); // sub sp,sp,#16
        image.Put(4, B(4, 64), 4);
        image.Put(8, 0x910043ff, 4); // add sp,sp,#16
        image.Put(12, 0xd65f03c0, 4);
        image.Put(64, 0xd28000e0, 4); // mov x0,#7
        image.Put(68, B(68, 8), 4);
        var result = Lift(image, range);
        checks.True(result.Function is { } body && body.Blocks.Single(b => b.End is Return).End is Return r
            && r.Results[0].Value.ConstantValue == 7, "补丁指令在原位置执行后顺序恢复栈并返回");
        checks.True(image.Functions.Single() == range && result.Function?.Blocks.All(b => b.Trace is null || b.Trace.NativeAddress < 16) == true,
            "补丁不进入函数范围或图中追溯地址");
        image.Put(68, B(68, 12), 4);
        checks.True(!Arm64LinkerFlow.TryPatch(image, range, 4, out _, out _) && Lift(image, range).Failure?.Reason.Code == "stack-restore",
            "第二条没有跳回原位置的下一条时不认补丁");
        image.Put(68, B(68, 8), 4);
        foreach (uint word in new uint[] { 0x10000000, 0x90000000, 0x58000040, B(64, 128) })
        {
            image.Put(64, word, 4);
            checks.True(!Arm64LinkerFlow.TryPatch(image, range, 4, out _, out _), "相对 PC 或控制流指令不能搬回原位置");
        }
        image.Put(64, 0xd28000e0, 4);
        checks.True(!Arm64LinkerFlow.TryPatch(image, range with { Length = 8 }, 4, out _, out _), "跳回函数末尾之外仍保持跨函数转移");
    }
    private static void Calls(Assertions checks)
    {
        var caller = new FunctionRange(0, 8, FunctionEvidence.UnwindTable);
        var image = new InputMemoryImage { Executable = true, Functions = [caller, new(128, 4, FunctionEvidence.UnwindTable), new(256, 4, FunctionEvidence.UnwindTable)] };
        image.Put(0, B(0, 64, true), 4); image.Put(4, 0xd65f03c0, 4);
        image.Put(64, B(64, 128), 4); image.Put(128, B(128, 256), 4); image.Put(256, 0xd65f03c0, 4);
        checks.True(Arm64DirectCalls.ResolveTarget(image, new ImageFunction(64)).Target == new ImageFunction(128), "空隙里的跳板归一到它转去的函数；只有一条跳转的函数保留自己的入口");
        checks.True(Arm64DirectCalls.ResolveTarget(image, new ImageFunction(128)).Target == new ImageFunction(128), "有展开信息的单指令函数不是跳板");
        checks.True(Lift(image, caller).Function?.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target == new ImageFunction(128),
            "原生调用产物使用归一后的地址");
        checks.True(Arm64DirectCalls.ToCandidates(image, caller, new HashSet<ulong> { 128 }).Single() == (0UL, 128UL), "运行时调用候选扫描使用相同的归一入口");

        InputMemoryImage Thunk(params uint[] words)
        {
            var source = new InputMemoryImage { Executable = true, Functions = [caller, new(256, 4, FunctionEvidence.UnwindTable)] };
            source.Put(0, B(0, 64, true), 4); source.Put(4, 0xd65f03c0, 4); source.Put(256, 0xd65f03c0, 4);
            for (int i = 0; i < words.Length; i++) source.Put(64 + (ulong)i * 4, words[i], 4);
            return source;
        }
        foreach (var source in new[]
        {
            Thunk(0x90000010, 0x91040210, 0xd61f0200), // adrp/add/br x16
            Thunk(0xd2802011, 0xd61f0220), // mov x17,#256; br x17
            Thunk(0xd2802010, 0xf2a00010, 0xd61f0200) // movz/movk/br x16
        })
            checks.True(Lift(source, caller).Function?.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target == new ImageFunction(256),
                "常量经链接器临时寄存器形成的范围扩展跳板归一");
        var effect = Thunk(0xd28000e0, B(68, 256));
        checks.True(Arm64DirectCalls.ResolveTarget(effect, new ImageFunction(64)).Target == new ImageFunction(64), "改写实参的序列不是调用跳板");
        var owned = new InputMemoryImage { Executable = true, Functions = [caller, new(64, 12, FunctionEvidence.UnwindTable)] };
        owned.Put(64, B(64, 256), 4); owned.Put(68, B(68, 256), 4);
        checks.True(Arm64DirectCalls.ResolveTarget(owned, new ImageFunction(64)).Target == new ImageFunction(64)
            && Arm64DirectCalls.ResolveTarget(owned, new ImageFunction(68)).Target == new ImageFunction(68), "已知多指令函数及其内部地址不归一成跳板");
        var cycle = Thunk(B(64, 80)); cycle.Put(80, B(80, 64), 4);
        checks.True(Lift(cycle, caller).Failure?.Reason.Code == "call-target.cycle", "调用跳板成环报告洞");
        var tailCycle = Thunk(B(64, 80)); tailCycle.Put(80, B(80, 64), 4); tailCycle.Put(0, B(0, 64), 4);
        checks.True(Lift(tailCycle, caller).Failure?.Reason.Code == "call-target.cycle", "直接尾调用的跳板环同样报告洞");
        var chain = Thunk(B(64, 68));
        for (ulong pc = 68; pc < 204; pc += 4) chain.Put(pc, B(pc, pc + 4), 4);
        checks.True(Arm64DirectCalls.ResolveTarget(chain, new ImageFunction(64)).Failure?.Code == "call-target.budget", "跳板链有确定的步数上限");
    }
}
