using System.Text.Json;
using Cpp2CS.Abi;
using Cpp2CS.Native;

public static class MachineEffectsChecks
{
    public static void Run(Action<bool, string> check)
    {
        check(Arm64Registers.Canonical("fp") == "x29" && Arm64Registers.Canonical("wsp") == "sp" &&
            Arm64Registers.Width("s3") == 32 && Arm64Registers.Width("v3") == 128, "ARM64 寄存器别名与位宽集中定义");
        check(Arm64Calls.HelperArgumentCount("RaiseException") == 1 && Arm64Calls.HelperArgumentCount("RethrowException") == 1 &&
            Arm64Calls.HelperArgumentCount("CxxThrow") == 3, "不返回的 helper 仍读取实际参数");
        check(Arm64Calls.HelperArgumentCount("AllocateArray") == 2 && Arm64Calls.HelperArgumentCount("WriteBarrier") == 1 &&
            Arm64Calls.HelperArgumentCount("unrecognized") is null, "helper 参数摘要不按名称缺省猜成一个参数");
        check(Arm64Registers.CallInputs.Contains("x8") && Arm64Registers.PreservedByCall("x29") == 64 &&
            Arm64Registers.PreservedByCall("v8") == 64 && Arm64Registers.PreservedByCall("x18") == 0, "调用保留 X8 输入及 X29、V8 的精确保存范围");
        var unsupported = new Instruction(0x100, "not-supported", "", [], false, false, "") { Writes = ["w3", "nzcv"] };
        var effects = Arm64Effects.Lower(unsupported);
        check(effects.Unsupported is not null && effects.Writes.ToHashSet().SetEquals(["x3", "nzcv", "memory"]) &&
            effects.Assignments.All(w => w.Value.Operation == "unknown"), "未知指令显式破坏目标、标志及内存，不沿用旧值");
        Operand Reg(string register) => new(1, register, 0, null, null, 0, 0, 0, 0);
        var shifted = new Instruction(0x104, "add", "", [Reg("x0"), Reg("x1"), Reg("x2") with { Shift = 2, ShiftKind = 2 }], false, false, "");
        check(Arm64Effects.Lower(shifted).Unsupported is not null, "未知移位类型不会偷偷按 LSL 解释");
        var fp = new Instruction(0x108, "add", "", [Reg("x0"), Reg("fp"), new(2, null, 8, null, null, 0, 0, 0, 0)], false, false, "");
        check(Arm64Effects.Lower(fp).Reads.Contains("x29"), "循环分析使用的机器读取集合包含帧指针");
    }
    public static void Export(string config, string binary, string output)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!;
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var effects = decoder.Decode(File.ReadAllBytes(binary), 0x100000).Select(Arm64Effects.Lower).ToArray();
        if (effects.Any(e => e.Unsupported is not null)) throw new InvalidOperationException(string.Join('\n', effects.Where(e => e.Unsupported is not null).Select(e => e.Source.Display + ": " + e.Unsupported)));
        File.WriteAllText(output, JsonSerializer.Serialize(effects));
    }
}
