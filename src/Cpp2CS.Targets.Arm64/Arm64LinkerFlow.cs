using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet : IInstructionFlowFacts
{
    public DecodeResult DecodeForFlow(ulong address, FunctionRange range) =>
        Arm64LinkerFlow.TryPatch(image, range, address, out _, out var word)
            ? DecodeWord(address, word, orderedMemory) : Decode(address);
    public CallTargetResolution ResolveCallTarget(CallTarget target) => Arm64DirectCalls.ResolveTarget(image, target);
}

/// <summary>只按指令形状还原搬移后跳回续点的链接器补丁。</summary>
public static class Arm64LinkerFlow
{
    internal static bool DirectBranch(IImage image, ulong address, out ulong target)
    {
        target = 0;
        if ((address & 3) != 0 || !image.IsExecutable(address, 4)) return false;
        uint word = (uint)image.ReadUnsigned(address, 4);
        if ((word & 0xfc000000) != 0x14000000) return false;
        long displacement = ((long)(word & 0x03ffffff) << 38) >> 36;
        target = unchecked(address + (ulong)displacement);
        return true;
    }

    public static bool TryPatch(IImage image, FunctionRange range, ulong address, out ulong patch, out uint instruction)
    {
        patch = 0; instruction = 0;
        bool Inside(ulong p) => p >= range.Start && p - range.Start < range.Length;
        // 续点必须仍在原函数内，否则它仍是一个跨函数转移。
        if (!Inside(address) || address > ulong.MaxValue - 4 || !Inside(address + 4)
            || !DirectBranch(image, address, out var target) || Inside(target)
            || target > ulong.MaxValue - 8 || !image.IsExecutable(target, 8)
            || !DirectBranch(image, target + 4, out var next) || next != address + 4) return false;
        uint word = (uint)image.ReadUnsigned(target, 4);
        // 分支/异常/系统组、ADR/ADRP、字面量访存不作为可原位执行的指令。
        if ((word & 0x1c000000) == 0x14000000 || (word & 0x1f000000) == 0x10000000
            || (word & 0x3b000000) == 0x18000000) return false;
        patch = target; instruction = word;
        return true;
    }
}
