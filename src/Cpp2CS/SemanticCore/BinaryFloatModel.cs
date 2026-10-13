using System.Numerics;

namespace Cpp2CS.SemanticCore;

public enum BinaryFloatKind
{
    Add, Sub, Mul, Div, Sqrt, Convert, FromSigned, FromUnsigned, ToSigned, ToUnsigned,
    RoundIntegral, RoundIntegralExact, Compare, CompareSignal,
    Minimum, Maximum, MinimumNumber, MaximumNumber, MinimumSecond, MaximumSecond,
    MulAdd, MulSub, NegMulAdd, NegMulSub, NegMul, AbsDiff
}
public enum BinaryFloatRounding { TiesEven, TiesAway, PlusInfinity, MinusInfinity, TowardZero }
public enum BinaryNaNRule { FirstSignalingThenFirst, First, Canonical }
public enum BinarySubnormalInput { Preserve, SignedZero }
public enum BinarySubnormalOutput { Preserve, SignedZeroBeforeRounding, SignedZeroAfterRounding }
public enum BinaryDenormalException { None, WhenFlushed, OnNumericUse }
public enum BinaryTininess { BeforeRounding, AfterRounding }
public enum BinaryInvalidInteger { Saturate, Minimum, Zero }

[Flags]
public enum BinaryFloatException : uint
{
    None = 0, Invalid = 1, DivideByZero = 2, Overflow = 4, Underflow = 8, Inexact = 16, InputDenormal = 32
}

// 所有规则均为值语义；没有宿主浮点状态或隐含的动态舍入模式。
public sealed record BinaryFloatRules
{
    public BinaryNaNRule NaN { get; init; } = BinaryNaNRule.FirstSignalingThenFirst;
    public bool InvalidNaNNegative { get; init; }
    public BinarySubnormalInput SubnormalInput { get; init; } = BinarySubnormalInput.Preserve;
    public BinarySubnormalOutput SubnormalOutput { get; init; } = BinarySubnormalOutput.Preserve;
    public BinaryDenormalException DenormalException { get; init; } = BinaryDenormalException.None;
    public BinaryTininess Tininess { get; init; } = BinaryTininess.AfterRounding;
    public bool ExactTinyUnderflow { get; init; }
    public bool FlushRaisesInexact { get; init; } = true;
    public BinaryInvalidInteger InvalidInteger { get; init; } = BinaryInvalidInteger.Saturate;
}

public sealed record BinaryFloatSpec(BinaryFloatKind Kind, int OperandWidth, int ResultWidth,
    BinaryFloatRounding Rounding, BinaryFloatRules Rules, int FractionBits = 0)
{
    public int InputCount => Kind switch
    {
        BinaryFloatKind.MulAdd or BinaryFloatKind.MulSub or BinaryFloatKind.NegMulAdd or BinaryFloatKind.NegMulSub => 3,
        BinaryFloatKind.Add or BinaryFloatKind.Sub or BinaryFloatKind.Mul or BinaryFloatKind.Div or BinaryFloatKind.NegMul or BinaryFloatKind.AbsDiff or
            BinaryFloatKind.Compare or BinaryFloatKind.CompareSignal or BinaryFloatKind.Minimum or BinaryFloatKind.Maximum or
            BinaryFloatKind.MinimumNumber or BinaryFloatKind.MaximumNumber or BinaryFloatKind.MinimumSecond or BinaryFloatKind.MaximumSecond => 2,
        _ => 1
    };
    public string? Validate()
    {
        if (!Enum.IsDefined(Kind) || !Enum.IsDefined(Rounding) || Rules is null) return "浮点操作、舍入或规则无效";
        if (!Enum.IsDefined(Rules.NaN) || !Enum.IsDefined(Rules.SubnormalInput) || !Enum.IsDefined(Rules.SubnormalOutput) ||
            !Enum.IsDefined(Rules.DenormalException) || !Enum.IsDefined(Rules.Tininess) || !Enum.IsDefined(Rules.InvalidInteger))
            return "浮点规则包含未定义枚举";
        var from = Kind is BinaryFloatKind.FromSigned or BinaryFloatKind.FromUnsigned;
        var to = Kind is BinaryFloatKind.ToSigned or BinaryFloatKind.ToUnsigned;
        if (from ? OperandWidth is < 1 or > 4096 : OperandWidth is not (16 or 32 or 64)) return "输入格式或整数宽度无效";
        if (to ? ResultWidth is < 1 or > 4096 : Kind is BinaryFloatKind.Compare or BinaryFloatKind.CompareSignal ? ResultWidth != 2 : ResultWidth is not (16 or 32 or 64))
            return "输出格式或整数宽度无效";
        if (!from && !to && Kind is not (BinaryFloatKind.Convert or BinaryFloatKind.Compare or BinaryFloatKind.CompareSignal) && OperandWidth != ResultWidth)
            return "算术输入与输出必须使用同一格式";
        if (FractionBits < 0 || FractionBits > (from ? OperandWidth : to ? ResultWidth : 0)) return "定点缩放超出整数宽度";
        return null;
    }
}

// Compare 的结果是中立的二位关系：0 相等，1 小于，2 大于，3 无序。
public readonly record struct BinaryFloatResult(BigInteger Bits, BinaryFloatException Exceptions);
