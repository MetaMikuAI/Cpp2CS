using Cpp2CS.Snapshot;

namespace Cpp2CS.Target;

/// <summary>AAPCS64 §6。内部下标 32..63 为 V 寄存器，64 为线程指针，65..68 为 N、Z、C、V。</summary>
public static class Abi
{
    public const int Thread = 64, Negative = 65, Zero = 66, Carry = 67, Overflow = 68, Count = 69;
    public static int Width(int r) => r is >= 32 and < 64 ? 128 : r >= Negative ? 1 : 64;
    public static Slot? Entry(int r) => r switch
    {
        < 8 => new(SlotKind.Integer, r),
        8 => new(SlotKind.IndirectResult, 0),
        >= 19 and <= 29 => new(SlotKind.Preserved, r - 19),
        30 => new(SlotKind.ReturnAddress, 0),
        31 => new(SlotKind.StackPointer, 0),
        >= 32 and < 40 => new(SlotKind.Vector, r - 32),
        >= 40 and < 48 => new(SlotKind.Preserved, r - 29),
        Thread => new(SlotKind.ThreadPointer, 0),
        _ => null
    };
    public static int Register(Slot s) => s.Kind switch
    {
        SlotKind.Integer => s.Index,
        SlotKind.IndirectResult => 8,
        SlotKind.Vector => 32 + s.Index,
        SlotKind.Preserved => s.Index < 11 ? 19 + s.Index : 29 + s.Index,
        SlotKind.ReturnAddress => 30,
        SlotKind.StackPointer => 31,
        SlotKind.ThreadPointer => Thread,
        SlotKind.Unwind => s.Index,
        _ => throw new ArgumentOutOfRangeException(nameof(s))
    };
    internal static readonly int[] Arguments = [0, 1, 2, 3, 4, 5, 6, 7, 8, 32, 33, 34, 35, 36, 37, 38, 39, 31];
    internal static readonly int[] Results = [0, 1, 32, 33, 34, 35];
    internal static readonly int[] Return = [.. Results, 30, 31, .. Enumerable.Range(19, 11), .. Enumerable.Range(40, 8)];
    internal static readonly int[] TailInputs = [.. Arguments, 30, .. Enumerable.Range(19, 11), .. Enumerable.Range(40, 8)];
    internal static (Slot Slot, int Width)[] Slots(IEnumerable<int> regs) =>
        regs.Select(r => (Entry(r)!.Value, r is >= 40 and < 48 ? 64 : Width(r))).ToArray();
}

public enum ArmOperation
{
    // DDI 0487：FPMulAdd，操作数依次为加数和两个乘数，只舍入一次。
    FusedMultiplyAdd = 1,
    // FPMax、FPMin、FPMaxNum、FPMinNum；依次按 Arm 的 NaN 与有符号零规则选择。
    Maximum, Minimum, MaximumNumber, MinimumNumber,
    // FPRoundInt：最近偶数、向正无穷、向负无穷、向零。
    RoundEven, RoundPositive, RoundNegative, RoundZero
}
