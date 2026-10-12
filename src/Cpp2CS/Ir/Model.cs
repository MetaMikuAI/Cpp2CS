using System.Numerics;

namespace Cpp2CS.Ir;

public sealed record InstructionOrigin
{
    public string ImageId { get; }
    public ulong Address { get; }
    public long FileOffset { get; }
    public ReadOnlyMemory<byte> Bytes { get; }

    public InstructionOrigin(string imageId, ulong address, long fileOffset, ReadOnlyMemory<byte> bytes)
    {
        ImageId = imageId;
        Address = address;
        FileOffset = fileOffset;
        Bytes = bytes.ToArray();
    }
}
public readonly record struct Value(int Id, int Width);
public enum SupportClass { Exact, NormalPathOnly, ExceptionBoundaryOnly }
public enum OpCode
{
    Constant, ReadSlot, WriteSlot, Extract, Concat, Zext, Sext,
    Add, Sub, Mul, And, Or, Xor, Not, Shl, Shr, Sar, Eq, Ult, Slt, Select,
    Load, Store, Undefined, UDiv, SDiv, Float, Guard
}
public enum FloatKind
{
    Add, Sub, Mul, Div, Sqrt, NegMul, AbsDiff,
    Min, Max, MinNumber, MaxNumber, Compare, CompareSignal,
    Convert, FromSigned, FromUnsigned, ToSigned, ToUnsigned,
    RoundIntegral, RoundIntegralExact
}
public enum FloatRounding { Current, TiesEven, PlusInfinity, MinusInfinity, TowardZero, TiesAway }
public sealed record FloatOperation(FloatKind Kind, int OperandWidth, int ResultWidth,
    FloatRounding Rounding = FloatRounding.Current);
// Flags 位 0..5：invalid、divide-by-zero、overflow、underflow、inexact、input-denormal。
public readonly record struct FloatResult(BigInteger Bits, uint Flags, uint TrapFlags)
{
    public FloatResult(BigInteger bits, uint flags) : this(bits, flags, flags) { }
}
public enum ExitKind { Next, Jump, Branch, Trap }
public enum FaultPolicy { None, StopUnmodeled }

public sealed record Operation(
    OpCode Code, Value? Result, Value[] Inputs, BigInteger Immediate = default,
    string? Slot = null, string? Detail = null, int WorldIn = -1, int WorldOut = -1,
    FaultPolicy Fault = FaultPolicy.None, FloatOperation? Floating = null);

public sealed record MirExit(ExitKind Kind, ulong Address = 0, Value? Target = null,
    Value? Condition = null, Value? Alternative = null, string? Reason = null,
    ulong? ResumeAddress = null)
{
    public static MirExit Next(ulong address) => new(ExitKind.Next, Address: address);
    public static MirExit Jump(Value target) => new(ExitKind.Jump, Target: target);
    public static MirExit Branch(Value condition, Value taken, Value notTaken) =>
        new(ExitKind.Branch, Target: taken, Condition: condition, Alternative: notTaken);
    public static MirExit Trap(string reason, ulong? resumeAddress = null) =>
        new(ExitKind.Trap, Reason: reason, ResumeAddress: resumeAddress);
}

public sealed record MirInstruction(Architecture Architecture, InstructionOrigin Origin, string Rule,
    IReadOnlyList<Operation> Operations, MirExit Exit, SupportClass Support, IReadOnlyList<string> Limitations);

public sealed record LiftResult(MirInstruction? Ir, string Form, string? Reason)
{
    public bool IsSupported => Ir is not null;
    public static LiftResult Supported(MirInstruction ir) => new(ir, ir.Rule, null);
    public static LiftResult Unsupported(string form, string reason) => new(null, form, reason);
}

public static class StateLayout
{
    public static IReadOnlyDictionary<string, int> For(Architecture architecture) => architecture == Architecture.Arm64 ? Arm : X64;

    private static readonly Dictionary<string, int> Arm = CreateArm();
    private static readonly Dictionary<string, int> X64 = CreateX64();

    private static Dictionary<string, int> CreateArm()
    {
        var slots = new Dictionary<string, int> { ["sp"] = 64, ["n"] = 1, ["z"] = 1, ["c"] = 1, ["v"] = 1, ["fpcr"] = 32, ["fpsr"] = 32 };
        for (var i = 0; i < 31; i++) slots.Add($"x{i}", 64);
        for (var i = 0; i < 32; i++) slots.Add($"v{i}", 128);
        slots.Add("tpidr_el0", 64);
        return slots;
    }

    private static Dictionary<string, int> CreateX64()
    {
        var slots = new Dictionary<string, int>();
        foreach (var name in new[] { "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "fsbase", "gsbase" }) slots.Add(name, 64);
        foreach (var name in new[] { "cf", "pf", "af", "zf", "sf", "of", "df" }) slots.Add(name, 1);
        for (var i = 0; i < 16; i++) slots.Add($"xmm{i}", 128);
        slots.Add("mxcsr", 32);
        return slots;
    }
}
