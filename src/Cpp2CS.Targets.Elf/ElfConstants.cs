using Cpp2CS.Native.Images;

namespace Cpp2CS.Targets.Elf;

internal static class ElfConstants
{
    internal const ushort AArch64 = 183, X86_64 = 62, EtExec = 2, EtDyn = 3;
    internal const byte Class64 = 2, LittleEndian = 1;
    internal const uint ArmNone = 0;
    internal const uint ArmAbs64 = 257;
    internal const uint ArmAbs32 = 258;
    internal const uint ArmAbs16 = 259;
    internal const uint ArmPrel64 = 260;
    internal const uint ArmPrel32 = 261;
    internal const uint ArmPrel16 = 262;
    internal const uint ArmMovwUabsG0 = 263;
    internal const uint ArmCondbr19 = 280;
    internal const uint ArmJump26 = 282;
    internal const uint ArmMovwPrelG3 = 293;
    internal const uint ArmMovwGotoffG0 = 300;
    internal const uint ArmMovwGotoffG3 = 306;
    internal const uint ArmGotrel64 = 307;
    internal const uint ArmGotrel32 = 308;
    internal const uint ArmGotLdPrel19 = 309;
    internal const uint ArmLd64GotLo12Nc = 312;
    internal const uint ArmTlsgdAdrPrel21 = 512;
    internal const uint ArmTlsleLdst64TprelLo12Nc = 559;
    internal const uint ArmGlobDat = 1025;
    internal const uint ArmJumpSlot = 1026;
    internal const uint ArmRelative = 1027;
    internal const uint ArmTlsDtpmod = 1028;
    internal const uint ArmTlsDtprel = 1029;
    internal const uint ArmTlsTprel = 1030;
    internal const uint ArmTlsdesc = 1031;
    internal const uint ArmIrelative = 1032;
    internal const uint X64None = 0;
    internal const uint X64Abs64 = 1;
    internal const uint X64Pc32 = 2;
    internal const uint X64GlobDat = 6;
    internal const uint X64JumpSlot = 7;
    internal const uint X64Relative = 8;
    internal const uint X64Abs32 = 10;
    internal const uint X64Abs32S = 11;
    internal const uint X64Dtpmod64 = 16;
    internal const uint X64Dtpoff64 = 17;
    internal const uint X64Tpoff64 = 18;
    internal const uint X64Tlsdesc = 36;
    internal const uint X64Irelative = 37;
    internal static RelocationKind Classify(ushort machine, uint kind) => machine switch
    {
        AArch64 => kind switch
        {
            ArmAbs64 or ArmGlobDat or ArmJumpSlot or ArmRelative => RelocationKind.Pointer,
            ArmIrelative => RelocationKind.Resolver,
            >= ArmTlsDtpmod and <= ArmTlsdesc => RelocationKind.ThreadStorage,
            ArmPrel64 or ArmPrel32 or ArmPrel16 => RelocationKind.RelativeDisplacement,
            _ => RelocationKind.Instruction
        },
        X86_64 => kind switch
        {
            X64Abs64 or X64GlobDat or X64JumpSlot or X64Relative => RelocationKind.Pointer,
            X64Irelative => RelocationKind.Resolver,
            X64Dtpmod64 or X64Dtpoff64 or X64Tpoff64 or X64Tlsdesc => RelocationKind.ThreadStorage,
            X64Pc32 => RelocationKind.RelativeDisplacement,
            _ => RelocationKind.Instruction
        },
        _ => throw new NotSupportedException($"ELF machine {machine} 未支持")
    };
}
