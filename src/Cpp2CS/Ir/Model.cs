using System.Numerics;
using System.Text.Json.Serialization;

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
public readonly record struct Value([property: JsonRequired] int Id, [property: JsonRequired] int Width);
public enum SupportClass { Exact, NormalPathOnly, ExceptionBoundaryOnly }
public enum OpCode
{
    Constant, ReadSlot, WriteSlot, Extract, Concat, Zext, Sext,
    Add, Sub, Mul, And, Or, Xor, Not, Shl, Shr, Sar, Eq, Ult, Slt, Select,
    Load, Store, Undefined, UDiv, SDiv, Float, Guard,
    LoadExclusive, StoreExclusive, ClearExclusive, Barrier, Prefetch, WriteProbe, Qarma5, CodeGuarded, FloatFused,
    LoadIf, StoreIf, AtomicRmw
}
public enum FloatKind
{
    Add, Sub, Mul, Div, Sqrt, NegMul, AbsDiff,
    Min, Max, MinNumber, MaxNumber, Compare, CompareSignal,
    Convert, FromSigned, FromUnsigned, ToSigned, ToUnsigned,
    RoundIntegral, RoundIntegralExact, MulAdd, MulSub, NegMulAdd, NegMulSub
}
public enum FloatRounding { Current, TiesEven, PlusInfinity, MinusInfinity, TowardZero, TiesAway }
public sealed record FloatOperation(FloatKind Kind, int OperandWidth, int ResultWidth,
    FloatRounding Rounding = FloatRounding.Current, int FractionBits = 0);
// Flags 位 0..5：invalid、divide-by-zero、overflow、underflow、inexact、input-denormal。
public readonly record struct FloatResult(BigInteger Bits, uint Flags, uint TrapFlags)
{
    public FloatResult(BigInteger bits, uint flags) : this(bits, flags, flags) { }
}
