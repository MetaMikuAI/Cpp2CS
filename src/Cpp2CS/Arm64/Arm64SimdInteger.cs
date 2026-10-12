using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private static Value Pack(Context c, IReadOnlyList<Value> lanes)
    {
        var result = lanes[0];
        for (var i = 1; i < lanes.Count; i++) result = c.B.Concat(lanes[i], result);
        return result;
    }

    private static LiftResult SimdNarrow(Context c)
    {
        var size = c.Field(22, 2);
        if (size == 3) return c.Reject("Reserved SIMD narrowing size");
        var elementWidth = 8 << size;
        var source = c.ReadVector(c.Rn, 128);
        var lanes = new List<Value>();
        for (var offset = 0; offset < 128; offset += elementWidth * 2)
            lanes.Add(c.B.Extract(source, offset, elementWidth));
        var result = Pack(c, lanes);
        c.WriteVector(c.Rd, c.Bit(30) ? c.B.Concat(result, c.ReadVector(c.Rd, 64)) : result);
        return c.Done();
    }

    private static LiftResult SimdReverse(Context c)
    {
        var width = c.Bit(30) ? 128 : 64;
        var elementWidth = 8 << c.Field(22, 2);
        var group = c.Bit(12) ? 16 : c.Bit(29) ? 32 : 64;
        if (elementWidth >= group) return c.Reject("Reserved SIMD reversal size");
        var source = c.ReadVector(c.Rn, width);
        var lanes = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
            lanes.Add(c.B.Extract(source, offset / group * group + group - elementWidth - offset % group, elementWidth));
        c.WriteVector(c.Rd, Pack(c, lanes));
        return c.Done();
    }

    private static LiftResult SimdPermute(Context c)
    {
        var width = c.Bit(30) ? 128 : 64;
        var elementWidth = 8 << c.Field(22, 2);
        if (elementWidth == width) return c.Reject("Reserved single-D permutation");
        var count = width / elementWidth;
        var left = c.ReadVector(c.Rn, width);
        var right = c.ReadVector(c.Rm, width);
        var concat = c.B.Concat(right, left);
        var upper = c.Bit(14) ? 1 : 0;
        var opcode = c.Field(12, 2);
        var lanes = new List<Value>();
        for (var i = 0; i < count; i++)
        {
            var source = (i & 1) == 0 ? left : right;
            var index = opcode == 3 ? upper * (count / 2) + i / 2 : i / 2 * 2 + upper;
            lanes.Add(opcode == 1 ? c.B.Extract(concat, (i * 2 + upper) * elementWidth, elementWidth) : c.B.Extract(source, index * elementWidth, elementWidth));
        }
        c.WriteVector(c.Rd, Pack(c, lanes));
        return c.Done();
    }

    private static LiftResult SimdIntegerBinary(Context c)
    {
        var scalar = c.Bit(28);
        var width = scalar ? 64 : c.Bit(30) ? 128 : 64;
        var elementWidth = 8 << c.Field(22, 2);
        var opcode = c.Field(10, 6);
        if (!scalar && elementWidth == 64 && (!c.Bit(30) || opcode is 25 or 27 or 39)) return c.Reject("Reserved SIMD integer binary size");
        var left = c.ReadVector(c.Rn, width);
        var right = c.ReadVector(c.Rm, width);
        var unsigned = c.Bit(29);
        var lanes = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
        {
            var a = c.B.Extract(left, offset, elementWidth);
            var b = c.B.Extract(right, offset, elementWidth);
            var zero = c.C(elementWidth, 0);
            Value result;
            if (opcode == 39) result = c.B.Mul(a, b);
            else if (opcode == 17)
            {
                var count = c.B.Sext(c.B.Extract(b, 0, 8), elementWidth);
                var negative = c.B.Slt(count, zero);
                var amount = c.B.Sub(zero, count);
                result = c.B.Select(negative, unsigned ? c.B.Shr(a, amount) : c.B.Sar(a, amount), c.B.Shl(a, count));
            }
            else if (opcode is 25 or 27)
            {
                var less = unsigned ? c.B.Ult(a, b) : c.B.Slt(a, b);
                result = opcode == 27 ? c.B.Select(less, a, b) : c.B.Select(less, b, a);
            }
            else
            {
                var condition = opcode == 35 ? unsigned ? c.B.Eq(a, b) : c.B.BoolNot(c.B.Eq(c.B.And(a, b), zero))
                    : opcode == 13 ? unsigned ? c.B.Ult(b, a) : c.B.Slt(b, a)
                    : c.B.BoolNot(unsigned ? c.B.Ult(a, b) : c.B.Slt(a, b));
                result = c.B.Select(condition, c.C(elementWidth, Mask(elementWidth)), zero);
            }
            lanes.Add(result);
        }
        c.WriteVector(c.Rd, Pack(c, lanes));
        return c.Done();
    }

    private static LiftResult SimdIntegerUnary(Context c)
    {
        var scalar = c.Bit(28);
        var width = scalar ? 64 : c.Bit(30) ? 128 : 64;
        var elementWidth = 8 << c.Field(22, 2);
        if (!scalar && elementWidth == width) return c.Reject("Reserved single-D integer unary operation");
        var opcode = c.Field(12, 4);
        var source = c.ReadVector(c.Rn, width);
        var lanes = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
        {
            var a = c.B.Extract(source, offset, elementWidth);
            var zero = c.C(elementWidth, 0);
            if (opcode == 11)
            {
                var negative = c.B.Sub(zero, a);
                lanes.Add(c.Bit(29) ? negative : c.B.Select(c.B.Slt(a, zero), negative, a));
                continue;
            }
            var condition = opcode == 8 ? c.Bit(29) ? c.B.BoolNot(c.B.Slt(a, zero)) : c.B.Slt(zero, a)
                : opcode == 9 ? c.Bit(29) ? c.B.BoolNot(c.B.Slt(zero, a)) : c.B.Eq(a, zero)
                : c.B.Slt(a, zero);
            lanes.Add(c.B.Select(condition, c.C(elementWidth, Mask(elementWidth)), zero));
        }
        c.WriteVector(c.Rd, Pack(c, lanes));
        return c.Done();
    }

    private static LiftResult SimdAddReduce(Context c)
    {
        var scalarPair = c.Bit(28);
        var pair = scalarPair || c.Bit(10);
        var width = c.Bit(30) ? 128 : 64;
        var elementWidth = 8 << c.Field(22, 2);
        if (!scalarPair && (elementWidth == 64 && (!pair || !c.Bit(30)) || !pair && elementWidth == 32 && !c.Bit(30)))
            return c.Reject("Reserved SIMD reduction size");
        var source = c.ReadVector(c.Rn, scalarPair ? 128 : width);
        var lanes = new List<Value>();
        if (pair)
        {
            if (!scalarPair) source = c.B.Concat(c.ReadVector(c.Rm, width), source);
            for (var offset = 0; offset < (scalarPair ? 128 : width * 2); offset += elementWidth * 2)
                lanes.Add(c.B.Add(c.B.Extract(source, offset, elementWidth), c.B.Extract(source, offset + elementWidth, elementWidth)));
        }
        else
        {
            var result = c.C(elementWidth, 0);
            for (var offset = 0; offset < width; offset += elementWidth) result = c.B.Add(result, c.B.Extract(source, offset, elementWidth));
            lanes.Add(result);
        }
        c.WriteVector(c.Rd, Pack(c, lanes));
        return c.Done();
    }

    private static LiftResult SimdShiftImmediate(Context c)
    {
        var immh = c.Field(19, 4);
        if (immh == 0) return c.Reject("Reserved SIMD shift immediate");
        var elementWidth = 8 << BitOperations.Log2((uint)immh);
        var opcode = c.Field(11, 5);
        var widen = opcode == 20;
        var narrow = opcode == 16;
        var scalar = c.Bit(28);
        if ((widen || narrow) && elementWidth == 64 || scalar && elementWidth != 64 || !scalar && !widen && !narrow && elementWidth == 64 && !c.Bit(30))
            return c.Reject("Reserved SIMD shift size");
        var width = scalar || widen ? 64 : narrow ? 128 : c.Bit(30) ? 128 : 64;
        var source = c.ReadVector(c.Rn, widen ? 128 : width);
        if (widen && c.Bit(30)) source = c.B.Extract(source, 64, 64);
        var inputWidth = narrow ? elementWidth * 2 : elementWidth;
        var outputWidth = widen ? elementWidth * 2 : elementWidth;
        var left = opcode is 10 or 20;
        var count = left ? c.Field(16, 7) - elementWidth : elementWidth * 2 - c.Field(16, 7);
        var lanes = new List<Value>();
        for (var offset = 0; offset < width; offset += inputWidth)
        {
            var element = c.B.Extract(source, offset, inputWidth);
            if (widen) element = c.Bit(29) ? c.B.Zext(element, outputWidth) : c.B.Sext(element, outputWidth);
            var amount = c.C(element.Width, (ulong)count);
            var result = left ? c.B.Shl(element, amount) : narrow || c.Bit(29) ? c.B.Shr(element, amount) : c.B.Sar(element, amount);
            lanes.Add(narrow ? c.B.Trunc(result, outputWidth) : result);
        }
        var data = Pack(c, lanes);
        c.WriteVector(c.Rd, narrow && c.Bit(30) ? c.B.Concat(data, c.ReadVector(c.Rd, 64)) : data);
        return c.Done();
    }

    private static LiftResult SimdMultiplyElement(Context c)
    {
        var size = c.Field(22, 2);
        if (size is not (1 or 2)) return c.Reject("Reserved indexed SIMD integer multiplication size");
        var elementWidth = 8 << size;
        var index = size == 1 ? (c.Bit(11) ? 4 : 0) | (c.Bit(21) ? 2 : 0) | (c.Bit(20) ? 1 : 0)
            : (c.Bit(11) ? 2 : 0) | (c.Bit(21) ? 1 : 0);
        var width = c.Bit(30) ? 128 : 64;
        var right = c.B.Extract(c.ReadVector(size == 1 ? c.Field(16, 4) : c.Rm, 128), index * elementWidth, elementWidth);
        var left = c.ReadVector(c.Rn, width);
        var lanes = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
            lanes.Add(c.B.Mul(c.B.Extract(left, offset, elementWidth), right));
        c.WriteVector(c.Rd, Pack(c, lanes));
        return c.Done();
    }

    private static LiftResult SimdAddWide(Context c)
    {
        var elementWidth = 8 << c.Field(22, 2);
        if (elementWidth == 64) return c.Reject("Reserved SIMD wide arithmetic size");
        var left = c.ReadVector(c.Rn, 128);
        var right = c.ReadVector(c.Rm, 128);
        var lanes = new List<Value>();
        for (var offset = 0; offset < 64; offset += elementWidth)
        {
            var a = c.B.Extract(left, offset * 2, elementWidth * 2);
            var b = c.B.Extract(right, (c.Bit(30) ? 64 : 0) + offset, elementWidth);
            b = c.Bit(29) ? c.B.Zext(b, elementWidth * 2) : c.B.Sext(b, elementWidth * 2);
            lanes.Add(c.Bit(13) ? c.B.Sub(a, b) : c.B.Add(a, b));
        }
        c.WriteVector(c.Rd, Pack(c, lanes));
        return c.Done();
    }
}
