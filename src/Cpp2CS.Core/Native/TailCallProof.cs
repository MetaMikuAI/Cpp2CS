using Cpp2CS.Abi;

namespace Cpp2CS.Native;

// 尾调用沿用当前返回协议；跳转目标已知只构成候选，不替代帧恢复证明。
public static class TailCallProof
{
    public static readonly string[] Registers = ["sp", "x30", .. Enumerable.Range(19, 11).Select(i => "x" + i), .. Enumerable.Range(8, 8).Select(i => "v" + i)];

    public static string? Check(SsaSemantics semantics, NativeMethod caller, ulong pc, NativeAbi abi)
    {
        var instruction = semantics.Program.Instructions.Single(i => i.Address == pc);
        var state = instruction.Effects.Select(semantics.Raw).SingleOrDefault(v => v.Operation == "tail-state");
        if (state is null || instruction.Call is not { } call) return "尾调用缺少机器状态";
        var target = semantics.TargetMethod(call);
        var outgoing = target is null ? null : abi.Classify(target);
        var helperArguments = Arm64Calls.HelperArgumentCount(semantics.Helper(call));
        if (abi.Classify(caller) is not { } incoming || outgoing is null && (helperArguments is null || caller.ReturnType != "void")) return "尾调用接口未确定";
        if (caller.ReturnType != "void" && (caller.ReturnType != target!.ReturnType || incoming.Return != outgoing!.Return) || incoming.Return.Indirect || outgoing?.Return.Indirect == true)
            return "尾调用返回接口不兼容或隐藏返回存储未证明";
        if (outgoing is not null && outgoing.StackBytes > incoming.StackBytes) return "尾调用栈实参超出入口保证的区域";
        for (var i = 0; i < Registers.Length; i++)
        {
            var register = Registers[i];
            var current = semantics.Resolve(state.Inputs[i]);
            var original = semantics.Resolve("entry_" + register);
            if (register.StartsWith('v')) { current = SsaSemantics.Slice(current, 0, 64); original = SsaSemantics.Slice(original, 0, 64); }
            if (current.Key != original.Key) return "尾调用未恢复入口状态：" + register;
        }
        foreach (var argument in outgoing?.Arguments ?? new([]))
        {
            var value = semantics.AbiArgument(call, argument);
            if (SsaSemantics.Contains(value, "stack") || argument.Indirect && SsaSemantics.Contains(semantics.AbiCarrier(call, argument), "stack"))
                return "尾调用实参仍引用当前栈帧";
        }
        if (outgoing is null && Enumerable.Range(0, helperArguments!.Value).Any(i => SsaSemantics.Contains(semantics.Argument(call, i), "stack")))
            return "尾调用 helper 实参仍引用当前栈帧";
        return null;
    }
}
