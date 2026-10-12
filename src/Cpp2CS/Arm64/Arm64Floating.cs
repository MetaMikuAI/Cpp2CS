using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private static LiftResult SystemRegister(Context c)
    {
        var encoding = c.Word & 0xFFDFFFE0;
        var slot = encoding == 0xD51B4400 ? "fpcr" : encoding == 0xD51B4420 ? "fpsr" : "tpidr_el0";
        var width = slot == "tpidr_el0" ? 64 : 32;
        var mask = slot == "fpcr" ? 0x07C09F00UL : slot == "fpsr" ? 0x0800009FUL : ulong.MaxValue;
        if (c.Bit(21))
        {
            var value = c.B.And(c.B.Read(slot, width), c.C(width, mask));
            c.Write(c.Rd, width == 64 ? value : c.B.Zext(value, 64));
        }
        else c.B.Write(slot, c.B.And(c.Read(c.Rd, width), c.C(width, mask)));
        return c.Done();
    }

    // The profile excludes AFP merging/alternative handling and FP16.
    private static LiftResult FloatUnary(Context c)
    {
        var type = c.Field(22, 2);
        if (type >= 2) return c.Reject("Reserved or unsupported FP16 unary operation");
        var width = 32 << type;
        var opcode = c.Field(15, 6);
        var source = c.ReadVector(c.Rn, width);
        if (opcode is 1 or 2)
        {
            var sign = c.C(width, 1UL << (width - 1));
            c.WriteVector(c.Rd, opcode == 1 ? c.B.And(source, c.B.Not(sign)) : c.B.Xor(source, sign));
            return c.Done();
        }
        FloatOperation spec;
        if (opcode == 3) spec = new(FloatKind.Sqrt, width, width);
        else if (opcode is 4 or 5)
        {
            var destinationWidth = 32 << (opcode & 1);
            if (destinationWidth == width) return c.Reject("Reserved equal-width floating conversion");
            spec = new(FloatKind.Convert, width, destinationWidth);
        }
        else if (opcode is >= 8 and <= 12 or 14 or 15)
        {
            var rounding = opcode switch
            {
                8 => FloatRounding.TiesEven,
                9 => FloatRounding.PlusInfinity,
                10 => FloatRounding.MinusInfinity,
                11 => FloatRounding.TowardZero,
                12 => FloatRounding.TiesAway,
                _ => FloatRounding.Current
            };
            spec = new(opcode == 14 ? FloatKind.RoundIntegralExact : FloatKind.RoundIntegral, width, width, rounding);
        }
        else return c.Reject("Unimplemented floating one-source opcode");
        var control = c.B.Read("fpcr", 32);
        var packed = c.B.Float(spec, source, c.C(width, 0), control);
        c.WriteVector(c.Rd, FloatingResult(c, packed, spec.ResultWidth, control));
        return c.Done();
    }

    private static LiftResult FloatVectorSign(Context c)
    {
        var width = c.Bit(30) ? 128 : 64;
        var elementWidth = c.Bit(22) ? 64 : 32;
        if (width < elementWidth * 2) return c.Reject("Reserved single-D vector sign operation");
        var sign = Replicate(c, c.C(elementWidth, 1UL << (elementWidth - 1)), width);
        var source = c.ReadVector(c.Rn, width);
        c.WriteVector(c.Rd, c.Bit(29) ? c.B.Xor(source, sign) : c.B.And(source, c.B.Not(sign)));
        return c.Done();
    }

    private static LiftResult FloatConditionalSelect(Context c)
    {
        var type = c.Field(22, 2);
        if (type >= 2) return c.Reject("Reserved or unsupported FP16 conditional select");
        var width = 32 << type;
        var value = c.B.Select(c.Condition(c.Field(12, 4)), c.ReadVector(c.Rn, width), c.ReadVector(c.Rm, width));
        c.WriteVector(c.Rd, value);
        return c.Done();
    }

    private static LiftResult FloatBinary(Context c)
    {
        var type = c.Field(22, 2);
        if (type >= 2) return c.Reject("Reserved or unsupported FP16 binary operation");
        var opcode = c.Field(12, 4);
        if (opcode > 8) return c.Reject("Reserved floating two-source opcode");
        var kind = opcode switch
        {
            0 => FloatKind.Mul,
            1 => FloatKind.Div,
            2 => FloatKind.Add,
            3 => FloatKind.Sub,
            4 => FloatKind.Max,
            5 => FloatKind.Min,
            6 => FloatKind.MaxNumber,
            7 => FloatKind.MinNumber,
            _ => FloatKind.NegMul
        };
        var width = 32 << type;
        var control = c.B.Read("fpcr", 32);
        var packed = c.B.Float(new(kind, width, width), c.ReadVector(c.Rn, width), c.ReadVector(c.Rm, width), control);
        c.WriteVector(c.Rd, FloatingResult(c, packed, width, control));
        return c.Done();
    }

    private static LiftResult FloatCompare(Context c, bool conditional)
    {
        var type = c.Field(22, 2);
        if (type >= 2) return c.Reject("Reserved or unsupported FP16 floating compare");
        var width = 32 << type;
        var control = c.B.Read("fpcr", 32);
        var kind = c.Bit(4) ? FloatKind.CompareSignal : FloatKind.Compare;
        var right = !conditional && c.Bit(3) ? c.C(width, 0) : c.ReadVector(c.Rm, width);
        var packed = c.B.Float(new(kind, width, 4), c.ReadVector(c.Rn, width), right, control);
        if (conditional) packed = c.B.Select(c.Condition(c.Field(12, 4)), packed, c.C(16, (ulong)c.Field(0, 4)));
        var flags = FloatingResult(c, packed, 4, control);
        var slots = new[] { "n", "z", "c", "v" };
        for (var i = 0; i < 4; i++) c.B.Write(slots[i], c.B.Extract(flags, 3 - i, 1));
        return c.Done();
    }

    private static LiftResult FloatIntegerConvert(Context c)
    {
        var type = c.Field(22, 2);
        if (type >= 2) return c.Reject("Reserved or unsupported FP16 integer conversion");
        var opcode = c.Field(16, 5);
        var floatWidth = 32 << type;
        var intWidth = c.Width;
        FloatOperation spec;
        Value source;
        if (opcode is 2 or 3)
        {
            spec = new(opcode == 2 ? FloatKind.FromSigned : FloatKind.FromUnsigned, intWidth, floatWidth);
            source = c.Read(c.Rn, intWidth);
        }
        else if (opcode is 0 or 1 or 4 or 5 or 8 or 9 or 16 or 17 or 24 or 25)
        {
            var rounding = (opcode & ~1) switch
            {
                0 => FloatRounding.TiesEven,
                4 => FloatRounding.TiesAway,
                8 => FloatRounding.PlusInfinity,
                16 => FloatRounding.MinusInfinity,
                _ => FloatRounding.TowardZero
            };
            spec = new((opcode & 1) == 0 ? FloatKind.ToSigned : FloatKind.ToUnsigned, floatWidth, intWidth, rounding);
            source = c.ReadVector(c.Rn, floatWidth);
        }
        else return c.Reject("Unimplemented integer/floating conversion opcode");
        var control = c.B.Read("fpcr", 32);
        var packed = c.B.Float(spec, source, c.C(spec.OperandWidth, 0), control);
        var result = FloatingResult(c, packed, spec.ResultWidth, control);
        if (opcode is 2 or 3) c.WriteVector(c.Rd, result);
        else c.Write(c.Rd, result);
        return c.Done();
    }

    private static LiftResult FloatVectorConvert(Context c)
    {
        var scalar = c.Bit(28);
        var elementWidth = c.Bit(22) ? 64 : 32;
        if (scalar && !c.Bit(30) || !scalar && elementWidth == 64 && !c.Bit(30))
            return c.Reject("Reserved SIMD floating conversion size");
        var width = scalar ? elementWidth : c.Bit(30) ? 128 : 64;
        var opcode = c.Word & 0x8FBFFC00;
        var fromInteger = opcode == 0x0E21D800;
        var kind = fromInteger ? c.Bit(29) ? FloatKind.FromUnsigned : FloatKind.FromSigned
            : c.Bit(29) ? FloatKind.ToUnsigned : FloatKind.ToSigned;
        var rounding = opcode switch
        {
            0x0E21A800 => FloatRounding.TiesEven,
            0x0E21B800 => FloatRounding.MinusInfinity,
            0x0EA1A800 => FloatRounding.PlusInfinity,
            0x0EA1B800 => FloatRounding.TowardZero,
            0x0E21C800 => FloatRounding.TiesAway,
            _ => FloatRounding.Current
        };
        var source = c.ReadVector(c.Rn, width);
        var control = c.B.Read("fpcr", 32);
        var results = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
            results.Add(c.B.Float(new(kind, elementWidth, elementWidth, rounding), c.B.Extract(source, offset, elementWidth), c.C(elementWidth, 0), control));
        c.WriteVector(c.Rd, FloatingLanes(c, results, elementWidth, control));
        return c.Done();
    }

    private static LiftResult FloatVectorBinary(Context c)
    {
        var scalar = c.Bit(28);
        var elementWidth = c.Bit(22) ? 64 : 32;
        if (!scalar && elementWidth == 64 && !c.Bit(30)) return c.Reject("Reserved single-D vector floating arithmetic");
        var width = scalar ? elementWidth : c.Bit(30) ? 128 : 64;
        var scalarPair = (c.Word & 0xFFBFFC00) == 0x7E30D800;
        var opcode = c.Word & 0xBFA0FC00;
        var pair = scalarPair || opcode == 0x2E20D400;
        var kind = opcode switch
        {
            0x0EA0D400 => FloatKind.Sub,
            0x2E20DC00 => FloatKind.Mul,
            0x2E20FC00 => FloatKind.Div,
            0x0E20F400 => FloatKind.Max,
            0x0EA0F400 => FloatKind.Min,
            0x0E20C400 => FloatKind.MaxNumber,
            0x0EA0C400 => FloatKind.MinNumber,
            0x2EA0D400 or 0x3EA0D400 => FloatKind.AbsDiff,
            _ => FloatKind.Add
        };
        var left = c.ReadVector(c.Rn, scalarPair ? elementWidth * 2 : width);
        var right = scalarPair ? left : c.ReadVector(c.Rm, width);
        var source = pair && !scalarPair ? c.B.Concat(right, left) : left;
        var control = c.B.Read("fpcr", 32);
        var results = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
        {
            var a = c.B.Extract(source, pair ? offset * 2 : offset, elementWidth);
            var b = pair ? c.B.Extract(source, offset * 2 + elementWidth, elementWidth) : c.B.Extract(right, offset, elementWidth);
            results.Add(c.B.Float(new(kind, elementWidth, elementWidth), a, b, control));
        }
        c.WriteVector(c.Rd, FloatingLanes(c, results, elementWidth, control));
        return c.Done();
    }

    private static LiftResult FloatVectorCompare(Context c, bool zero)
    {
        var scalar = c.Bit(28);
        var elementWidth = c.Bit(22) ? 64 : 32;
        if (!scalar && elementWidth == 64 && !c.Bit(30)) return c.Reject("Reserved single-D vector floating comparison");
        var width = scalar ? elementWidth : c.Bit(30) ? 128 : 64;
        var opcode = (c.Word & 0xBFBFFC00) & ~0x10000000u;
        var equal = zero ? opcode == 0x0EA0D800 : !c.Bit(29);
        var reverse = zero && opcode is 0x2EA0D800 or 0x0EA0E800;
        var orEqual = zero ? opcode is 0x2EA0C800 or 0x2EA0D800 : !c.Bit(23);
        var kind = equal ? FloatKind.Compare : FloatKind.CompareSignal;
        var left = c.ReadVector(c.Rn, width);
        var right = zero ? c.C(width, 0) : c.ReadVector(c.Rm, width);
        var control = c.B.Read("fpcr", 32);
        var results = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
        {
            var a = c.B.Extract(left, offset, elementWidth);
            var b = c.B.Extract(right, offset, elementWidth);
            var comparison = c.B.Float(new(kind, elementWidth, 4), reverse ? b : a, reverse ? a : b, control);
            var flags = c.B.Extract(comparison, 0, 4);
            var condition = equal ? c.B.Eq(flags, c.C(4, 6)) : c.B.Eq(flags, c.C(4, 2));
            if (!equal && orEqual) condition = c.B.Or(condition, c.B.Eq(flags, c.C(4, 6)));
            var data = c.B.Select(condition, c.C(elementWidth, Mask(elementWidth)), c.C(elementWidth, 0));
            results.Add(c.B.Concat(c.B.Extract(comparison, 4, 12), data));
        }
        c.WriteVector(c.Rd, FloatingLanes(c, results, elementWidth, control));
        return c.Done();
    }

    private static LiftResult FloatVectorPrecision(Context c)
    {
        var widen = c.Bit(12);
        var inputWidth = widen ? 32 : 64;
        var outputWidth = widen ? 64 : 32;
        var source = c.ReadVector(c.Rn, 128);
        var offset = widen && c.Bit(30) ? 64 : 0;
        var control = c.B.Read("fpcr", 32);
        var results = new List<Value>();
        for (var i = 0; i < 2; i++)
            results.Add(c.B.Float(new(FloatKind.Convert, inputWidth, outputWidth), c.B.Extract(source, offset + i * inputWidth, inputWidth), c.C(inputWidth, 0), control));
        var data = FloatingLanes(c, results, outputWidth, control);
        c.WriteVector(c.Rd, !widen && c.Bit(30) ? c.B.Concat(data, c.ReadVector(c.Rd, 64)) : data);
        return c.Done();
    }

    private static LiftResult FloatMultiplyElement(Context c)
    {
        var size = c.Field(22, 2);
        if (size < 2 || size == 3 && c.Bit(21)) return c.Reject("Reserved or unsupported FP16 indexed multiply");
        var elementWidth = size == 2 ? 32 : 64;
        var scalar = c.Bit(28);
        if (!scalar && elementWidth == 64 && !c.Bit(30)) return c.Reject("Reserved single-D indexed floating multiply");
        var width = scalar ? elementWidth : c.Bit(30) ? 128 : 64;
        var index = size == 2 ? (c.Bit(11) ? 2 : 0) | (c.Bit(21) ? 1 : 0) : c.Bit(11) ? 1 : 0;
        var right = c.B.Extract(c.ReadVector(c.Rm, 128), index * elementWidth, elementWidth);
        var left = c.ReadVector(c.Rn, width);
        var control = c.B.Read("fpcr", 32);
        var results = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
            results.Add(c.B.Float(new(FloatKind.Mul, elementWidth, elementWidth), c.B.Extract(left, offset, elementWidth), right, control));
        c.WriteVector(c.Rd, FloatingLanes(c, results, elementWidth, control));
        return c.Done();
    }

    private static LiftResult FloatVectorUnary(Context c)
    {
        var width = c.Bit(30) ? 128 : 64;
        var elementWidth = c.Bit(22) ? 64 : 32;
        if (width == elementWidth) return c.Reject("Reserved single-D vector floating unary operation");
        var opcode = c.Word & 0xBFBFFC00;
        var kind = opcode == 0x2EA1F800 ? FloatKind.Sqrt : opcode == 0x2E219800 ? FloatKind.RoundIntegralExact : FloatKind.RoundIntegral;
        var rounding = opcode switch
        {
            0x0E218800 => FloatRounding.TiesEven,
            0x0EA18800 => FloatRounding.PlusInfinity,
            0x0E219800 => FloatRounding.MinusInfinity,
            0x0EA19800 => FloatRounding.TowardZero,
            0x2E218800 => FloatRounding.TiesAway,
            _ => FloatRounding.Current
        };
        var source = c.ReadVector(c.Rn, width);
        var control = c.B.Read("fpcr", 32);
        var results = new List<Value>();
        for (var offset = 0; offset < width; offset += elementWidth)
            results.Add(c.B.Float(new(kind, elementWidth, elementWidth, rounding), c.B.Extract(source, offset, elementWidth), c.C(elementWidth, 0), control));
        c.WriteVector(c.Rd, FloatingLanes(c, results, elementWidth, control));
        return c.Done();
    }

    private static Value FloatingLanes(Context c, IReadOnlyList<Value> lanes, int elementWidth, Value control)
    {
        Value? data = null;
        var flags = c.C(6, 0);
        var traps = c.C(6, 0);
        foreach (var lane in lanes)
        {
            var element = c.B.Extract(lane, 0, elementWidth);
            data = data is { } previous ? c.B.Concat(element, previous) : element;
            flags = c.B.Or(flags, c.B.Extract(lane, elementWidth, 6));
            traps = c.B.Or(traps, c.B.Extract(lane, elementWidth + 6, 6));
        }
        var packed = c.B.Concat(traps, c.B.Concat(flags, data!.Value));
        return FloatingResult(c, packed, data.Value.Width, control);
    }

    private static Value FloatingResult(Context c, Value packed, int width, Value control)
    {
        var flags = c.B.Extract(packed, width, 6);
        var traps = c.B.Extract(packed, width + 6, 6);
        var enabled = c.B.Or(c.B.Zext(c.B.Extract(control, 8, 5), 6), c.B.Shl(c.B.Zext(c.B.Extract(control, 15, 1), 6), c.C(6, 5)));
        c.B.Guard(c.B.Eq(c.B.And(traps, enabled), c.C(6, 0)), "enabled ARM floating-point exception");
        var cumulative = c.B.Or(c.B.Zext(c.B.Extract(flags, 0, 5), 32), c.B.Shl(c.B.Zext(c.B.Extract(flags, 5, 1), 32), c.C(32, 7)));
        c.B.Write("fpsr", c.B.Or(c.B.Read("fpsr", 32), cumulative));
        return c.B.Extract(packed, 0, width);
    }
}
