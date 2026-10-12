namespace Cpp2CS.Ir;

public sealed record MachineProfile(string Id, Architecture Architecture, string Endian, int AddressBits,
    ulong LoadBias, string ExecutionMode, string MemoryModel, string FaultModel, string[] Assumptions)
{
    public static MachineProfile For(Architecture architecture) => architecture == Architecture.Arm64
        ? new("aarch64-le-el0-v1", architecture, "little", 64, 0, "EL0; A64; FP/AdvSIMD enabled",
            "ordered byte-addressed accesses; single-thread observations", "unmodeled memory fault stops",
            ["image addresses are execution addresses", "no PAC/MTE/SVE/SME/BTI/GCS", "no tagged addresses", "SA0=0; FP/AdvSIMD access is permitted", "next-instruction fetch is outside this instruction transition", "permissions/alignment/data-abort effects are unmodeled", "atomic and barrier instructions unsupported"])
        : new("x64-le-user-v2", architecture, "little", 64, 0, "64-bit long mode; CPL3; CET disabled; SSE/SSE2 enabled",
            "ordered byte-addressed accesses; single-thread observations", "unmodeled memory/target fault stops",
            ["preferred image addresses are execution addresses", "48-bit canonical addresses; LA57 disabled", "FS/GS bases are explicit inputs", "SSE/SSE2 available; CR0.EM=0; CR0.TS=0; CR4.OSFXSR=1", "legacy SSE only; vector state above 128 bits is preserved and not represented", "next-instruction fetch is outside this instruction transition", "permissions/alignment/page-fault effects are unmodeled", "atomic/transactional instructions unsupported", "FP arithmetic unsupported"]);
}
