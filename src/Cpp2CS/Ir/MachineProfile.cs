using System.Collections.Immutable;

namespace Cpp2CS.Ir;

public sealed record MachineProfile(string Id, Architecture Architecture, string Endian, int AddressBits,
    ulong LoadBias, string ExecutionMode, string MemoryModel, string FaultModel, ImmutableArray<string> Assumptions)
{
    public static MachineProfile For(Architecture architecture) => architecture switch
    {
        Architecture.Arm64 => Arm64, Architecture.X64 => X64,
        _ => throw new ArgumentOutOfRangeException(nameof(architecture))
    };

    private static readonly MachineProfile Arm64 = new("aarch64-le-el0-v3", Architecture.Arm64, "little", 64, 0, "EL0; A64; FP/AdvSIMD, classic PAuth and BTI available",
            "explicit ordered memory events, reservations and external decisions; one concrete execution witness",
            "missing environment inputs and unmodeled faults stop explicitly",
            ["image addresses are execution addresses", "no MTE/SVE/SME/GCS/AFP/FP16/EBF",
             "48-bit VA; TBI=0; classic QARMA5; no EPAC/PAuth2/FPAC/PAuth_LR; HCR/SCR API and APK permit pointer authentication",
             "APIA/APIB keys and EnIA/EnIB are explicit inputs; authentication failure poisons the pointer",
             "BTI page attributes use explicit 4 KiB page keys; BTYPE and BT0 are explicit inputs",
             "SA0=0; nAA=0; FP/AdvSIMD access is permitted; binary32/binary64",
             "FP exception-enable bits are represented; enabled exception delivery stops explicitly",
             "exclusive store needs an explicit global-monitor decision; external writes and monitor invalidations are explicit events",
             "atomic width, memory order and barriers are retained; the concrete interpreter does not enumerate weak-memory executions",
             "next-instruction fetch is outside this instruction transition; fault delivery and handler state are unmodeled",
             "the binary does not establish these runtime configuration assumptions"]);
    private static readonly MachineProfile X64 = new("x64-le-user-v6", Architecture.X64, "little", 64, 0, "64-bit long mode; CPL3; CET disabled; SSE through SSE4.2, AVX/AVX2/FMA enabled; outside RTM and SGX enclaves",
            "explicit ordered byte-addressed events; one concrete execution witness", "unmodeled memory/target fault stops",
            ["preferred image addresses are execution addresses", "48-bit canonical addresses; LA57 disabled", "FS/GS bases are explicit inputs",
             "SSE through SSE4.2, AVX/AVX2/FMA and DAZ available; CR0.EM=0; CR0.TS=0; CR4.OSFXSR=1; CR4.OSXSAVE=1; XCR0.x87/SSE/AVX=1",
             "LAHF/SAHF available in 64-bit mode; BMI1 available (TZCNT does not fall back to BSF)",
             "PREFETCHW available; prefetch hints are NTA=0, T0=1, T1=2, T2=3, W=8",
             "XMM and YMM upper halves are represented separately; legacy SSE preserves upper halves; VEX.128 clears them; AVX-512 and AVX10 absent",
             "CS/ES/SS/DS/FS/GS selectors are explicit 16-bit inputs, independent of FS/GS bases; segment loading is unmodeled",
             "MXCSR controls and exception flags are represented; enabled exception delivery stops explicitly",
             "non-temporal stores and fences retain event metadata; write probes require explicit permissions",
             "next-instruction fetch is outside this instruction transition; permissions/alignment/page-fault delivery is unmodeled",
             "exception exits describe the event and saved instruction pointer, not IDT checks, delivery or handlers",
             "HLE disabled; CX16 available; locked operations use ordinary WB memory and explicit write permissions",
             "locked RMW/CAS is one indivisible event; memory order is retained without a concurrent-execution solver",
             "split-lock, alignment and bus-lock exception delivery is unmodeled; RTM instructions remain unsupported"]);
}
