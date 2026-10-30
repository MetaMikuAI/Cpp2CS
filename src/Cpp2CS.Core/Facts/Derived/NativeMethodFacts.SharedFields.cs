using Cpp2CS.Facts;

namespace Cpp2CS.Facts.Derived;

internal sealed partial class NativeMethodFacts
{
    // IL2CPP 的共享字段写入模板：固定宽度存储或按运行时大小复制，随后通知 GC。
    internal int SharedFieldSetter(ulong address)
    {
        uint W(int offset) => facts.Code.Word(address + (uint)offset) ?? 0;
        ulong Target(int offset) => A64.Imm26Target(W(offset), address + (uint)offset);
        bool Barrier(ulong target)
        {
            if (facts.Code.Word(target) == 0xaa0103e0 && facts.Code.Word(target + 4) is { } jump && A64.IsB(jump))
                target = A64.Imm26Target(jump, target + 4);
            return facts.Helpers.InternalCall(target).Kind == HelperKind.WriteBarrier;
        }
        if (W(0) != 0xa9be57fe || W(4) != 0xa9014ff4) return 0;
        if (W(8) == 0xaa0103f4 && W(12) == 0xaa0003f5 && W(20) == 0xaa1403e0
            && A64.IsBl(W(28)) && facts.Code.Word(Target(28)) == 0xd65f03c0
            && W(32) == 0xaa1503e0 && W(36) == 0xaa1403e1 && A64.IsBl(W(40))
            && facts.Helpers.InternalCall(Target(40)).Kind == HelperKind.FieldAddress
            && W(48) == 0xaa0003e1 && W(52) == 0xf9400680 && W(56) == 0xa9414ff4
            && W(60) == 0xaa1f03e2 && W(64) == 0xa8c257fe && A64.IsB(W(68)) && Barrier(Target(68)))
        {
            if (W(16) == 0x52800101 && W(24) == 0xaa0203f3 && W(44) == 0xf9000013) return 64;
            if (W(16) == 0x52800081 && W(24) == 0x2a0203f3 && W(44) == 0xb9000013) return 32;
        }
        if (W(8) == 0xaa0203f3 && W(12) == 0x2a0303f4 && A64.IsBl(W(16))
            && facts.Helpers.InternalCall(Target(16)).Kind == HelperKind.FieldAddress
            && W(20) == 0xaa1303e1 && W(24) == 0xaa1403e2 && W(28) == 0xaa0003f5
            && A64.IsBl(W(32)) && facts.Code.At(Target(32))?.Import == "memcpy"
            && W(36) == 0xa9414ff4 && W(40) == 0xaa1503e0 && W(44) == 0xa8c257fe
            && A64.IsB(W(48)) && Barrier(Target(48))) return -1;
        return 0;
    }
}
