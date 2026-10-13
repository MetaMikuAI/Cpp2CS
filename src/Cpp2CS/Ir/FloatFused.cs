using System.Numerics;

namespace Cpp2CS.Ir;

public static partial class FloatEvaluator
{
    // Intel SDM 14.5.2: a,b are multiplicand/multiplier; c is the addend.
    // Signs affect arithmetic only; NaN priority and payload remain a, b, then c.
    public static FloatResult EvaluateFused(Architecture architecture, FloatOperation spec,
        BigInteger a, BigInteger b, BigInteger c, uint control)
    {
        if (architecture != Architecture.X64 || spec.OperandWidth is not (32 or 64) ||
            spec.ResultWidth != spec.OperandWidth || spec.FractionBits != 0 || spec.Rounding != FloatRounding.Current ||
            spec.Kind is not (FloatKind.MulAdd or FloatKind.MulSub or FloatKind.NegMulAdd or FloatKind.NegMulSub))
            throw new InvalidOperationException("Unsupported fused floating operation");
        var format = GetFormat(spec.OperandWidth);
        var rounding = ResolveRounding(architecture, spec.Rounding, control);
        uint flags = 0;
        var left = Unpack(architecture, format, a, control, ref flags);
        var right = Unpack(architecture, format, b, control, ref flags);
        var addend = Unpack(architecture, format, c, control, ref flags);
        if (left.NaN || right.NaN || addend.NaN)
        {
            if (left.Signaling || right.Signaling || addend.Signaling) flags |= Invalid;
            var source = left.NaN ? left : right.NaN ? right : addend;
            return new(source.Bits | format.Quiet, flags);
        }
        if (left.Infinity && right.Zero || right.Infinity && left.Zero)
            return InvalidResult(architecture, format, flags);
        var productNegative = left.Negative ^ right.Negative ^
            (spec.Kind is FloatKind.NegMulAdd or FloatKind.NegMulSub);
        var addendNegative = addend.Negative ^ (spec.Kind is FloatKind.MulSub or FloatKind.NegMulSub);
        var productInfinite = left.Infinity || right.Infinity;
        if (productInfinite && addend.Infinity && productNegative != addendNegative)
            return InvalidResult(architecture, format, flags);
        flags |= DenormalFlags(architecture, left, right) | DenormalFlags(architecture, addend, default);
        if (productInfinite || addend.Infinity)
            return new(Signed(format.Infinity, productInfinite ? productNegative : addendNegative, format), flags);

        var product = left.Mantissa * right.Mantissa;
        var productExponent = left.Exponent + right.Exponent;
        var exponent = Math.Min(productExponent, addend.Exponent);
        var p = product << (productExponent - exponent);
        var z = addend.Mantissa << (addend.Exponent - exponent);
        var sum = (productNegative ? -p : p) + (addendNegative ? -z : z);
        var negative = sum.Sign < 0 || sum.IsZero &&
            (product.IsZero && addend.Zero && productNegative == addendNegative
                ? productNegative : rounding == FloatRounding.MinusInfinity);
        return Round(architecture, format, negative, BigInteger.Abs(sum), BigInteger.One,
            exponent, rounding, control, flags);
    }
}
