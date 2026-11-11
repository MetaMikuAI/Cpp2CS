using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet : INoReturnInstructionSet
{
    public bool IsStraightLineFailure(Reason reason) => reason.Code is
        "arm64.floating" or "arm64.vector" or "arm64.exclusive" or "arm64.atomic" or "arm64.barrier";

    // AArch64 ELF PLT：ADRP x16; LDR x17,[x16,#lo12]; ADD x16,x16,#lo12; BR x17。
    // 同时核对 ADD 与 LDR 的槽地址；导入身份仅来自映像重定位。
    public CallTarget ResolveCallTarget(IImage source, CallTarget target)
    {
        if (target is not ImageFunction f || !source.IsExecutable(f.EntryOffset, 16)) return target;
        ulong pc = f.EntryOffset;
        uint a = (uint)source.ReadUnsigned(pc, 4), b = (uint)source.ReadUnsigned(pc + 4, 4),
            c = (uint)source.ReadUnsigned(pc + 8, 4), d = (uint)source.ReadUnsigned(pc + 12, 4);
        if ((a & 0x9f00001f) != 0x90000010 || (b & 0xffc003ff) != 0xf9400211 ||
            (c & 0xffc003ff) != 0x91000210 || d != 0xd61f0220) return target;
        long immediate = (long)(((a >> 5) & 0x7ffff) << 2 | ((a >> 29) & 3));
        immediate = (immediate << 43) >> 43;
        ulong offset = ((b >> 10) & 4095) * 8UL;
        if (offset != ((c >> 10) & 4095)) return target;
        ulong slot = unchecked((pc & ~4095UL) + (ulong)(immediate << 12) + offset);
        if (source.Query(slot).AvailableBytes < 8) return target;
        return source.ReadPointer(slot) switch
        {
            PointerTarget.Import { Addend: 0 } import => new ImportedTarget(import.Symbol),
            PointerTarget.Internal inner => new ImageFunction(inner.Offset),
            _ => target
        };
    }
}
