using System.Numerics;
using Cpp2CS.Native.Terms;
using static Cpp2CS.Native.Terms.CoreOperation;
using static Cpp2CS.Targets.Arm64.Arm64Registers;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet
{
    private sealed partial class Semantics
    {
        private Term ReadV(int index, int width) => T.Slice(e.Read(V[index]), 0, width);
        private Term Convert(CoreOperation op, Term value, int width) => T.Apply(new CoreOperator(op), width, value);
        private static BigInteger FloatImmediate(int imm, int width)
        {
            int fraction = width == 32 ? 23 : 52, exponent = width == 32 ? 8 : 11;
            int b = (imm >> 6) & 1;
            return ((BigInteger)(imm >> 7) << (width - 1)) |
                ((BigInteger)(((1 - b) << (exponent - 1)) | (b * ((1 << (exponent - 3)) - 1) << 2) | ((imm >> 4) & 3)) << fraction) |
                ((BigInteger)(imm & 15) << (fraction - 4));
        }
        private Term SignalingNaN(Term value)
        {
            int fraction = value.Width == 32 ? 23 : 52;
            return Op(And, Compare(FloatUnordered, value, value), Unary(Not, T.Slice(value, fraction - 1, 1)));
        }
        private Term FloatMinMax(Term a, Term b, bool maximum, bool number)
        {
            var regular = Op(maximum ? FloatMaximum : FloatMinimum, a, b);
            return number ? Choose(Op(Or, SignalingNaN(a), SignalingNaN(b)), regular,
                Op(maximum ? FloatMaximumNumber : FloatMinimumNumber, a, b)) : regular;
        }
        private Term[] FloatFlags(Term a, Term b) =>
            [Compare(FloatLess, a, b), Compare(FloatEqual, a, b), Unary(Not, Compare(FloatLess, a, b)), Compare(FloatUnordered, a, b)];
        // 核心转换对越界未定义；先取整，再以精确的二次幂边界选择架构饱和值。
        private Term FloatInteger(Term value, int width, bool unsigned)
        {
            var rounded = Unary(FloatTruncate, value);
            var limit = Convert(UnsignedToFloat, K(BigInteger.One << (unsigned ? width : width - 1), width + 1), value.Width);
            var minimum = unsigned ? K(0, width) : K(BigInteger.One << (width - 1), width);
            var maximum = K((BigInteger.One << (unsigned ? width : width - 1)) - 1, width);
            var converted = Convert(unsigned ? FloatToUnsigned : FloatToSigned, rounded, width);
            converted = Choose(Compare(FloatLessEqual, limit, rounded), maximum, converted);
            converted = Choose(Compare(FloatLessEqual, rounded, unsigned ? K(0, value.Width) : Unary(FloatNegate, limit)), minimum, converted);
            return Choose(Compare(FloatUnordered, value, value), K(0, width), converted);
        }
        private bool Floating()
        {
            if (!Is(0x5e000000, 0x1e000000)) return false;
            int type = B(22, 2), width = type == 0 ? 32 : 64;
            if (type > 1) { Hole("floating"); return true; }
            var a = ReadV(A, width);
            if (Is(0xff000000, 0x1f000000))
            {
                var b = ReadV(M, width); var c = ReadV(B(10, 5), width);
                if (Bit(21)) c = Unary(FloatNegate, c);
                if (Bit(21) != Bit(15)) a = Unary(FloatNegate, a);
                WriteV(D, T.Apply(new CoreOperator(FloatFusedMultiplyAdd), width, a, b, c)); return true;
            }
            if (Is(0xff201fe0, 0x1e201000)) { WriteV(D, K(FloatImmediate(B(13, 8), width), width)); return true; }
            if (Is(0xff207c00, 0x1e204000))
            {
                int opcode = B(15, 6);
                if (opcode == 0) WriteV(D, a);
                else if (opcode is 4 or 5 && opcode != 4 + type) WriteV(D, Convert(FloatConvert, a, opcode == 4 ? 32 : 64));
                else if (opcode is 1 or 2 or 3 or 8 or 9 or 10 or 11 or 14 or 15)
                    WriteV(D, Unary(opcode switch { 1 => FloatAbs, 2 => FloatNegate, 3 => FloatSqrt, 9 => FloatCeiling, 10 => FloatFloor, 11 => FloatTruncate, _ => FloatRoundToEven }, a));
                else Hole("floating");
                return true;
            }
            if (Is(0xff200c00, 0x1e200800))
            {
                int opcode = B(12, 4); var b = ReadV(M, width);
                if (opcode <= 3 || opcode == 8)
                {
                    var result = Op(opcode switch { 0 or 8 => FloatMultiply, 1 => FloatDivide, 2 => FloatAdd, _ => FloatSubtract }, a, b);
                    WriteV(D, opcode == 8 ? Unary(FloatNegate, result) : result);
                }
                else if (opcode is >= 4 and <= 7) WriteV(D, FloatMinMax(a, b, (opcode & 1) == 0, opcode >= 6));
                else Hole("floating");
                return true;
            }
            if (Is(0xff20fc07, 0x1e202000))
            {
                if (Bit(3) && M != 0) Hole("floating");
                else Flags(FloatFlags(a, Bit(3) ? K(0, width) : ReadV(M, width)));
                return true;
            }
            if (Is(0xff200c00, 0x1e200400))
            {
                var condition = Condition(B(12, 4));
                Flags(FloatFlags(a, ReadV(M, width)).Select((f, i) => Choose(condition, f, K(B(3 - i), 1))).ToArray()); return true;
            }
            if (Is(0xff200c00, 0x1e200c00)) { WriteV(D, Choose(Condition(B(12, 4)), a, ReadV(M, width))); return true; }
            if (Is(0x7f200000, 0x1e000000))
            {
                int opcode = B(16, 3), rounding = B(19, 2), scale = B(10, 6);
                if (opcode != 0 || rounding != 3 || (Width == 32 && scale < 32))
                    Hole("floating", $"浮点转定点：sf={B(31)} type={type} rmode={rounding} opcode={opcode} scale={scale}");
                else
                {
                    int fracbits = 64 - scale, fraction = width == 32 ? 23 : 52, bias = width == 32 ? 127 : 1023;
                    // 乘以精确的二次幂后沿用饱和转整数；浮点溢出仍选择同一饱和值。
                    var scaled = Op(FloatMultiply, a, K((BigInteger)(bias + fracbits) << fraction, width));
                    WriteX(D, FloatInteger(scaled, Width, false));
                }
                return true;
            }
            if (Is(0x7f20fc00, 0x1e200000))
            {
                int opcode = B(16, 3), rounding = B(19, 2);
                if (rounding == 0 && opcode is 2 or 3)
                    WriteV(D, Convert(opcode == 2 ? SignedToFloat : UnsignedToFloat, ReadX(A, Width), width));
                else if (rounding == 0 && opcode is 6 or 7 && Width == width)
                {
                    if (opcode == 6) WriteX(D, a); else WriteV(D, ReadX(A, Width));
                }
                else if (opcode <= 1)
                {
                    var rounded = rounding switch { 0 => Unary(FloatRoundToEven, a), 1 => Unary(FloatCeiling, a), 2 => Unary(FloatFloor, a), _ => a };
                    WriteX(D, FloatInteger(rounded, Width, opcode == 1));
                }
                else Hole("floating");
                return true;
            }
            Hole("floating"); return true;
        }
    }
}
