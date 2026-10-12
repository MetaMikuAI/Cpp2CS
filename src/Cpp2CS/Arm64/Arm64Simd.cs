using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    // Arm A64 2025-09: DUP/INS/SMOV/UMOV, pp. 959-962, 1258-1261, 1464-1465, 1681-1682.
    private static LiftResult SimdCopy(Context c)
    {
        var imm5 = c.Field(16, 5);
        if ((imm5 & 15) == 0) return c.Reject("Reserved SIMD element size");
        var size = BitOperations.TrailingZeroCount((uint)imm5);
        var elementWidth = 8 << size;
        var index = imm5 >> (size + 1);
        var q = c.Bit(30);
        var opcode = c.Field(11, 4);
        if (c.Bit(29))
        {
            var sourceIndex = opcode >> size;
            var source = c.B.Extract(c.ReadVector(c.Rn, 128), sourceIndex * elementWidth, elementWidth);
            var old = c.ReadVector(c.Rd, 128);
            c.WriteVector(c.Rd, Insert(c, old, source, index * elementWidth));
            return c.Done();
        }
        if (opcode is 5 or 7)
        {
            var destinationWidth = q ? 64 : 32;
            if (opcode == 5 && elementWidth >= destinationWidth || opcode == 7 && (q ? elementWidth != 64 : elementWidth >= 64))
                return c.Reject("Reserved SIMD element-to-general width");
            var element = c.B.Extract(c.ReadVector(c.Rn, 128), index * elementWidth, elementWidth);
            c.Write(c.Rd, opcode == 5 ? c.B.Sext(element, destinationWidth) : c.B.Zext(element, destinationWidth));
            return c.Done();
        }
        if (opcode == 3)
        {
            var element = c.Read(c.Rn, elementWidth);
            c.WriteVector(c.Rd, Insert(c, c.ReadVector(c.Rd, 128), element, index * elementWidth));
            return c.Done();
        }
        var scalar = c.Bit(28);
        if (!scalar && elementWidth == 64 && !q) return c.Reject("Reserved single-D vector duplicate");
        var value = opcode == 1 ? c.Read(c.Rn, elementWidth) : c.B.Extract(c.ReadVector(c.Rn, 128), index * elementWidth, elementWidth);
        c.WriteVector(c.Rd, scalar ? value : Replicate(c, value, q ? 128 : 64));
        return c.Done();
    }

    private static Value Insert(Context c, Value destination, Value element, int offset)
    {
        var result = offset == 0 ? element : c.B.Concat(element, c.B.Extract(destination, 0, offset));
        var upper = destination.Width - offset - element.Width;
        return upper == 0 ? result : c.B.Concat(c.B.Extract(destination, offset + element.Width, upper), result);
    }

    private static Value Replicate(Context c, Value element, int width)
    {
        var result = element;
        while (result.Width < width) result = c.B.Concat(result, result);
        return result;
    }

    private static LiftResult SimdLogic(Context c)
    {
        var width = c.Bit(30) ? 128 : 64;
        var left = c.ReadVector(c.Rn, width);
        var right = c.ReadVector(c.Rm, width);
        var opcode = (c.Bit(29) ? 4 : 0) | c.Field(22, 2);
        Value result;
        if (opcode < 4)
        {
            if ((opcode & 1) != 0) right = c.B.Not(right);
            result = opcode < 2 ? c.B.And(left, right) : c.B.Or(left, right);
        }
        else if (opcode == 4) result = c.B.Xor(left, right);
        else
        {
            var old = c.ReadVector(c.Rd, width);
            result = opcode switch
            {
                5 => c.B.Or(c.B.And(old, left), c.B.And(c.B.Not(old), right)),
                6 => c.B.Or(c.B.And(right, left), c.B.And(c.B.Not(right), old)),
                7 => c.B.Or(c.B.And(c.B.Not(right), left), c.B.And(right, old)),
                _ => throw new InvalidOperationException()
            };
        }
        c.WriteVector(c.Rd, result);
        return c.Done();
    }

    private static LiftResult SimdNot(Context c)
    {
        c.WriteVector(c.Rd, c.B.Not(c.ReadVector(c.Rn, c.Bit(30) ? 128 : 64)));
        return c.Done();
    }

    private static LiftResult SimdExtract(Context c)
    {
        var width = c.Bit(30) ? 128 : 64;
        var offset = c.Field(11, 4) * 8;
        if (offset >= width) return c.Reject("Reserved 64-bit vector extract index");
        var low = c.ReadVector(c.Rn, width);
        var high = c.ReadVector(c.Rm, width);
        c.WriteVector(c.Rd, c.B.Extract(c.B.Concat(high, low), offset, width));
        return c.Done();
    }

    private static LiftResult SimdAddSubtract(Context c)
    {
        var scalar = c.Bit(28);
        var width = scalar ? 64 : c.Bit(30) ? 128 : 64;
        var elementWidth = 8 << c.Field(22, 2);
        if (!scalar && width == 64 && elementWidth == 64) return c.Reject("Reserved single-D vector arithmetic");
        var left = c.ReadVector(c.Rn, width);
        var right = c.ReadVector(c.Rm, width);
        Value? result = null;
        for (var offset = 0; offset < width; offset += elementWidth)
        {
            var a = c.B.Extract(left, offset, elementWidth);
            var b = c.B.Extract(right, offset, elementWidth);
            var element = c.Bit(29) ? c.B.Sub(a, b) : c.B.Add(a, b);
            result = result is { } previous ? c.B.Concat(element, previous) : element;
        }
        c.WriteVector(c.Rd, result!.Value);
        return c.Done();
    }

    // AdvSIMDExpandImm and VFPExpandImm construct bit patterns; no host floating-point operation is used.
    private static LiftResult SimdImmediate(Context c)
    {
        var cmode = c.Field(12, 4);
        var op = c.Bit(29);
        var q = c.Bit(30);
        if (cmode == 15 && op && !q) return c.Reject("Reserved single-D vector floating immediate");
        var immediate = (c.Field(16, 3) << 5) | c.Field(5, 5);
        int elementWidth;
        ulong bits;
        if (cmode < 8)
        {
            elementWidth = 32;
            bits = (ulong)immediate << (8 * (cmode >> 1));
        }
        else if (cmode < 12)
        {
            elementWidth = 16;
            bits = (ulong)immediate << (8 * ((cmode >> 1) & 1));
        }
        else if (cmode < 14)
        {
            elementWidth = 32;
            var shift = cmode == 12 ? 8 : 16;
            bits = ((ulong)immediate << shift) | Mask(shift);
        }
        else if (cmode == 14 && !op)
        {
            elementWidth = 8;
            bits = (ulong)immediate;
        }
        else if (cmode == 14)
        {
            elementWidth = 64;
            bits = 0;
            for (var i = 0; i < 8; i++) if ((immediate & (1 << i)) != 0) bits |= 0xFFUL << (i * 8);
        }
        else
        {
            elementWidth = op ? 64 : 32;
            bits = ExpandFloatImmediate(immediate, elementWidth);
        }
        var width = q ? 128 : 64;
        var expanded = Replicate(c, c.C(elementWidth, bits), width);
        Value result;
        if (cmode < 12 && (cmode & 1) != 0)
        {
            var old = c.ReadVector(c.Rd, width);
            result = op ? c.B.And(old, c.B.Not(expanded)) : c.B.Or(old, expanded);
        }
        else result = cmode < 14 && op ? c.B.Not(expanded) : expanded;
        c.WriteVector(c.Rd, result);
        return c.Done();
    }

    private static ulong ExpandFloatImmediate(int immediate, int width)
    {
        var exponentWidth = width == 32 ? 8 : 11;
        var fractionWidth = width - exponentWidth - 1;
        var raw = (uint)immediate;
        var repeated = (raw >> 6) & 1;
        var exponent = ((ulong)(1 - repeated) << (exponentWidth - 1)) |
                       ((repeated != 0 ? Mask(exponentWidth - 3) : 0) << 2) | ((raw >> 4) & 3);
        return ((ulong)(raw >> 7) << (width - 1)) | (exponent << fractionWidth) | ((ulong)(raw & 15) << (fractionWidth - 4));
    }

    private static LiftResult FloatMoveGeneral(Context c)
    {
        var upper = c.Field(22, 2) == 2;
        var width = c.Bit(31) ? 64 : 32;
        if (c.Bit(16))
        {
            var source = c.Read(c.Rn, width);
            c.WriteVector(c.Rd, upper ? c.B.Concat(source, c.ReadVector(c.Rd, 64)) : source);
        }
        else
        {
            var source = c.ReadVector(c.Rn, upper ? 128 : width);
            c.Write(c.Rd, upper ? c.B.Extract(source, 64, 64) : source);
        }
        return c.Done();
    }

    private static LiftResult FloatMoveRegister(Context c)
    {
        var type = c.Field(22, 2);
        if (type >= 2) return c.Reject("Reserved or unsupported FP16 register move");
        c.WriteVector(c.Rd, c.ReadVector(c.Rn, type == 0 ? 32 : 64));
        return c.Done();
    }

    private static LiftResult FloatMoveImmediate(Context c)
    {
        var type = c.Field(22, 2);
        if (type >= 2) return c.Reject("Reserved or unsupported FP16 immediate move");
        var width = type == 0 ? 32 : 64;
        c.WriteVector(c.Rd, c.C(width, ExpandFloatImmediate(c.Field(13, 8), width)));
        return c.Done();
    }

    private static LiftResult MultiplyLong(Context c)
    {
        var left = c.Read(c.Rn, 32);
        var right = c.Read(c.Rm, 32);
        left = c.Bit(23) ? c.B.Zext(left, 64) : c.B.Sext(left, 64);
        right = c.Bit(23) ? c.B.Zext(right, 64) : c.B.Sext(right, 64);
        var addend = c.Read(c.Field(10, 5), 64);
        var product = c.B.Mul(left, right);
        c.Write(c.Rd, c.Bit(15) ? c.B.Sub(addend, product) : c.B.Add(addend, product));
        return c.Done();
    }

    private static LiftResult MultiplyHigh(Context c)
    {
        var left = c.Read(c.Rn, 64);
        var right = c.Read(c.Rm, 64);
        left = c.Bit(23) ? c.B.Zext(left, 128) : c.B.Sext(left, 128);
        right = c.Bit(23) ? c.B.Zext(right, 128) : c.B.Sext(right, 128);
        c.Write(c.Rd, c.B.Extract(c.B.Mul(left, right), 64, 64));
        return c.Done();
    }
}
