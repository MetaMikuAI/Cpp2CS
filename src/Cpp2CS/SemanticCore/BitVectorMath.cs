using System.Numerics;

namespace Cpp2CS.SemanticCore;

public static class BitVectorMath
{
    public static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
    public static BigInteger Wrap(BigInteger value, int width) => value & Mask(width);
    public static BigInteger Signed(BigInteger value, int width) => value.TestBit(width - 1) ? value - (BigInteger.One << width) : value;
    public static BigInteger ShiftLeft(BigInteger value, BigInteger count, int width) => count >= width ? 0 : Wrap(value << (int)count, width);
    public static BigInteger ShiftRight(BigInteger value, BigInteger count, int width) => count >= width ? 0 : value >> (int)count;
    public static BigInteger ArithmeticRight(BigInteger value, BigInteger count, int width) =>
        Wrap(count >= width ? (Signed(value, width).Sign < 0 ? -1 : 0) : Signed(value, width) >> (int)count, width);
    public static BigInteger UnsignedDivide(BigInteger left, BigInteger right) => right.IsZero ? 0 : left / right;
    public static BigInteger SignedDivide(BigInteger left, BigInteger right, int width) =>
        right.IsZero ? 0 : Wrap(Signed(left, width) / Signed(right, width), width);
    private static bool TestBit(this BigInteger value, int bit) => ((value >> bit) & BigInteger.One) != 0;
}
