using System.Numerics;

namespace Cpp2CS.Ir;

// Integer/rational evaluation of binary32 and binary64. No host floating-point arithmetic.
// Arm ARM: FPUnpack, FPProcessNaNs, FPRoundBase, FPToFixed (FEAT_AFP absent).
// Intel SDM vol. 1: 4.8.3.5, 4.9.2, 10.2.3, 11.5.2 (legacy SSE).
public static class FloatEvaluator
{
    public const uint Invalid = 1, DivideByZero = 2, Overflow = 4,
        Underflow = 8, Inexact = 16, InputDenormal = 32;

    private readonly record struct Format(int Width, int Fraction, int Bias)
    {
        public int Minimum => 1 - Bias;
        public int Maximum => Bias;
        public ulong Sign => 1UL << (Width - 1);
        public ulong FractionMask => (1UL << Fraction) - 1;
        public ulong Infinity => (ulong)(2 * Bias + 1) << Fraction;
        public ulong Quiet => 1UL << (Fraction - 1);
    }

    private readonly record struct Number(ulong Bits, bool Negative, BigInteger Mantissa,
        int Exponent, bool Infinity, bool NaN, bool Signaling, bool Denormal)
    {
        public bool Zero => !Infinity && !NaN && Mantissa.IsZero;
    }

    public static FloatResult Evaluate(Architecture architecture, FloatOperation spec,
        BigInteger a, BigInteger b, uint control)
    {
        if (!ValidFractionBits(architecture, spec))
            throw new InvalidOperationException("Invalid fixed-point conversion scale or rounding mode");
        var input = GetFormat(spec.OperandWidth);
        var rounding = ResolveRounding(architecture, spec.Rounding, control);
        if (spec.Kind is FloatKind.NegMul or FloatKind.AbsDiff)
        {
            var nested = Evaluate(architecture, spec with
            {
                Kind = spec.Kind == FloatKind.NegMul ? FloatKind.Mul : FloatKind.Sub
            }, a, b, control);
            return nested with { Bits = spec.Kind == FloatKind.NegMul
                ? nested.Bits ^ input.Sign : nested.Bits & (input.Sign - 1) };
        }

        if (spec.Kind is FloatKind.FromSigned or FloatKind.FromUnsigned)
        {
            var integer = a & Mask(spec.OperandWidth);
            if (spec.Kind == FloatKind.FromSigned && integer.TestBit(spec.OperandWidth - 1))
                integer -= BigInteger.One << spec.OperandWidth;
            return Round(architecture, GetFormat(spec.ResultWidth), integer.Sign < 0,
                BigInteger.Abs(integer), BigInteger.One, -spec.FractionBits, rounding, control, 0);
        }

        uint flags = 0;
        var left = Unpack(architecture, input, a, control, ref flags);
        var binary = spec.Kind is FloatKind.Add or FloatKind.Sub or FloatKind.Mul or FloatKind.Div
            or FloatKind.Min or FloatKind.Max or FloatKind.MinNumber or FloatKind.MaxNumber
            or FloatKind.Compare or FloatKind.CompareSignal;
        var right = binary ? Unpack(architecture, input, b, control, ref flags) : default;

        if (spec.Kind is FloatKind.ToSigned or FloatKind.ToUnsigned)
            return ToInteger(architecture, spec, left, rounding, flags);

        if (spec.Kind is FloatKind.Compare or FloatKind.CompareSignal)
        {
            if (left.NaN || right.NaN)
            {
                if (left.Signaling || right.Signaling || spec.Kind == FloatKind.CompareSignal)
                    flags |= Invalid;
                return new(3, flags);
            }
            flags |= DenormalFlags(architecture, left, right);
            var order = Compare(left, right);
            return new(order < 0 ? 8 : order > 0 ? 2 : 6, flags);
        }

        if (spec.Kind is FloatKind.Min or FloatKind.Max or FloatKind.MinNumber or FloatKind.MaxNumber)
            return MinMax(architecture, spec.Kind, input, left, right, control, flags);

        var output = GetFormat(spec.ResultWidth);
        if (left.NaN || (binary && right.NaN))
            return PropagateNaN(architecture, input, output, left, right, control, flags);

        if (spec.Kind == FloatKind.Convert)
        {
            flags |= DenormalFlags(architecture, left, default);
            if (left.Infinity) return new(Signed(output.Infinity, left.Negative, output), flags);
            return Round(architecture, output, left.Negative, left.Mantissa,
                BigInteger.One, left.Exponent, rounding, control, flags);
        }

        if (spec.Kind is FloatKind.RoundIntegral or FloatKind.RoundIntegralExact)
        {
            if (left.Infinity || left.Zero) return new(left.Bits, flags);
            var integer = RoundInteger(left.Mantissa, BigInteger.One, left.Exponent,
                left.Negative, rounding, out var inexact);
            if (inexact && spec.Kind == FloatKind.RoundIntegralExact) flags |= Inexact;
            return Round(architecture, output, left.Negative, integer,
                BigInteger.One, 0, FloatRounding.TowardZero, control, flags);
        }

        if (spec.Kind == FloatKind.Sqrt)
        {
            if (left.Zero) return new(left.Bits, flags);
            if (left.Negative) return InvalidResult(architecture, output, flags);
            flags |= DenormalFlags(architecture, left, default);
            if (left.Infinity) return new(output.Infinity, flags);
            return SquareRoot(architecture, output, left, rounding, control, flags);
        }

        var sign = left.Negative ^ right.Negative;
        switch (spec.Kind)
        {
            case FloatKind.Add:
            case FloatKind.Sub:
            {
                var rightSign = right.Negative ^ (spec.Kind == FloatKind.Sub);
                if (left.Infinity && right.Infinity && left.Negative != rightSign)
                    return InvalidResult(architecture, output, flags);
                flags |= DenormalFlags(architecture, left, right);
                if (left.Infinity || right.Infinity)
                    return new(Signed(output.Infinity, left.Infinity ? left.Negative : rightSign, output), flags);
                var exponent = Math.Min(left.Exponent, right.Exponent);
                var l = left.Mantissa << (left.Exponent - exponent);
                var r = right.Mantissa << (right.Exponent - exponent);
                var sum = (left.Negative ? -l : l) + (rightSign ? -r : r);
                var negative = sum.Sign < 0 || (sum.IsZero &&
                    (left.Zero && right.Zero && left.Negative == rightSign
                        ? left.Negative : rounding == FloatRounding.MinusInfinity));
                return Round(architecture, output, negative, BigInteger.Abs(sum),
                    BigInteger.One, exponent, rounding, control, flags);
            }
            case FloatKind.Mul:
                if ((left.Infinity && right.Zero) || (right.Infinity && left.Zero))
                    return InvalidResult(architecture, output, flags);
                flags |= DenormalFlags(architecture, left, right);
                if (left.Infinity || right.Infinity) return new(Signed(output.Infinity, sign, output), flags);
                return Round(architecture, output, sign, left.Mantissa * right.Mantissa,
                    BigInteger.One, left.Exponent + right.Exponent, rounding, control, flags);
            case FloatKind.Div:
                if ((left.Infinity && right.Infinity) || (left.Zero && right.Zero))
                    return InvalidResult(architecture, output, flags);
                if (right.Zero && !left.Infinity)
                    return new(Signed(output.Infinity, sign, output), flags | DivideByZero);
                flags |= DenormalFlags(architecture, left, right);
                if (left.Infinity) return new(Signed(output.Infinity, sign, output), flags);
                if (left.Zero || right.Infinity) return new(Signed(0, sign, output), flags);
                return Round(architecture, output, sign, left.Mantissa, right.Mantissa,
                    left.Exponent - right.Exponent, rounding, control, flags);
            default:
                throw new InvalidOperationException($"Unsupported floating operation {spec.Kind}");
        }
    }

    private static FloatResult MinMax(Architecture architecture, FloatKind kind, Format format,
        Number left, Number right, uint control, uint flags)
    {
        var minimum = kind is FloatKind.Min or FloatKind.MinNumber;
        if (architecture == Architecture.X64)
        {
            if (kind is FloatKind.MinNumber or FloatKind.MaxNumber)
                throw new InvalidOperationException("Legacy SSE has no minimumNumber/maximumNumber instruction");
            if (left.NaN || right.NaN) return new(right.Bits, flags | Invalid);
            flags |= DenormalFlags(architecture, left, right);
            var order = Compare(left, right);
            return new((minimum ? order < 0 : order > 0) ? left.Bits : right.Bits, flags);
        }
        if (kind is FloatKind.MinNumber or FloatKind.MaxNumber)
        {
            if (left.NaN && !left.Signaling && !right.NaN) return new(right.Bits, flags);
            if (right.NaN && !right.Signaling && !left.NaN) return new(left.Bits, flags);
        }
        if (left.NaN || right.NaN)
            return PropagateNaN(architecture, format, format, left, right, control, flags);
        if (left.Zero && right.Zero)
            return new(Signed(0, minimum ? left.Negative || right.Negative
                : left.Negative && right.Negative, format), flags);
        var comparison = Compare(left, right);
        return new((minimum ? comparison < 0 : comparison > 0) ? left.Bits : right.Bits, flags);
    }

    private static FloatResult ToInteger(Architecture architecture, FloatOperation spec,
        Number value, FloatRounding rounding, uint flags)
    {
        var unsigned = spec.Kind == FloatKind.ToUnsigned;
        if (architecture == Architecture.X64 && unsigned)
            throw new InvalidOperationException("Legacy SSE has no unsigned integer conversion");
        var minimum = unsigned ? BigInteger.Zero : -(BigInteger.One << (spec.ResultWidth - 1));
        var maximum = (BigInteger.One << (spec.ResultWidth - (unsigned ? 0 : 1))) - 1;
        if (value.NaN || value.Infinity)
        {
            var invalid = architecture == Architecture.X64 ? minimum
                : value.NaN ? BigInteger.Zero : value.Negative ? minimum : maximum;
            return new(invalid & Mask(spec.ResultWidth), flags | Invalid);
        }
        var integer = RoundInteger(value.Mantissa, BigInteger.One, value.Exponent + spec.FractionBits,
            value.Negative, rounding, out var inexact);
        if (value.Negative) integer = -integer;
        if (integer < minimum || integer > maximum)
        {
            integer = architecture == Architecture.X64 ? minimum : BigInteger.Clamp(integer, minimum, maximum);
            return new(integer & Mask(spec.ResultWidth), flags | Invalid);
        }
        return new(integer & Mask(spec.ResultWidth), flags | (inexact ? Inexact : 0));
    }

    private static FloatResult PropagateNaN(Architecture architecture, Format input, Format output,
        Number left, Number right, uint control, uint flags)
    {
        if (left.Signaling || right.Signaling) flags |= Invalid;
        if (architecture == Architecture.Arm64 && (control & (1U << 25)) != 0)
            return new(output.Infinity | output.Quiet, flags);
        var source = architecture == Architecture.Arm64
            ? left.Signaling ? left : right.Signaling ? right : left.NaN ? left : right
            : left.NaN ? left : right;
        var payload = new BigInteger(source.Bits & input.FractionMask);
        payload = output.Fraction >= input.Fraction ? payload << (output.Fraction - input.Fraction)
            : payload >> (input.Fraction - output.Fraction);
        return new(Signed(output.Infinity | output.Quiet | (ulong)payload, source.Negative, output), flags);
    }

    private static FloatResult InvalidResult(Architecture architecture, Format format, uint flags) =>
        new(format.Infinity | format.Quiet | (architecture == Architecture.X64 ? format.Sign : 0), flags | Invalid);

    private static FloatResult Round(Architecture architecture, Format format, bool negative,
        BigInteger numerator, BigInteger denominator, int exponent, FloatRounding rounding,
        uint control, uint flags)
    {
        if (numerator.IsZero) return new(Signed(0, negative, format), flags);
        var binaryExponent = FloorLog2(numerator, denominator) + exponent;
        var tinyBefore = binaryExponent < format.Minimum;
        if (architecture == Architecture.Arm64 && tinyBefore && (control & (1U << 24)) != 0)
            return new(Signed(0, negative, format), flags | Underflow, flags);

        var unconstrained = RoundInteger(numerator, denominator,
            exponent - binaryExponent + format.Fraction, negative, rounding, out _);
        var roundedExponent = binaryExponent + (unconstrained >= (BigInteger.One << (format.Fraction + 1)) ? 1 : 0);
        if (roundedExponent > format.Maximum)
        {
            var infinity = rounding is FloatRounding.TiesEven or FloatRounding.TiesAway ||
                (rounding == FloatRounding.PlusInfinity && !negative) ||
                (rounding == FloatRounding.MinusInfinity && negative);
            return new(Signed(infinity ? format.Infinity : format.Infinity - 1, negative, format),
                flags | Overflow | Inexact);
        }

        var tiny = architecture == Architecture.Arm64 ? tinyBefore : roundedExponent < format.Minimum;
        var underflowEnabled = architecture == Architecture.Arm64
            ? (control & (1U << 11)) != 0 : (control & (1U << 11)) == 0;
        if (architecture == Architecture.X64 && tiny && !underflowEnabled && (control & (1U << 15)) != 0)
            return new(Signed(0, negative, format), flags | Underflow | Inexact);

        var quantum = Math.Max(binaryExponent, format.Minimum) - format.Fraction;
        var mantissa = RoundInteger(numerator, denominator, exponent - quantum,
            negative, rounding, out var inexact);
        if (inexact) flags |= Inexact;
        if (tiny && (inexact || underflowEnabled)) flags |= Underflow;
        if (mantissa.IsZero) return new(Signed(0, negative, format), flags);
        var resultExponent = Math.Max(binaryExponent, format.Minimum);
        if (mantissa >= (BigInteger.One << (format.Fraction + 1)))
        {
            mantissa >>= 1;
            resultExponent++;
        }
        var encodedExponent = mantissa < (BigInteger.One << format.Fraction) ? 0 : resultExponent + format.Bias;
        var bits = ((ulong)encodedExponent << format.Fraction) | ((ulong)mantissa & format.FractionMask);
        return new(Signed(bits, negative, format), flags);
    }

    private static FloatResult SquareRoot(Architecture architecture, Format format, Number value,
        FloatRounding rounding, uint control, uint flags)
    {
        var exponent = FloorLog2(value.Mantissa, BigInteger.One) + value.Exponent;
        var rootExponent = exponent >= 0 ? exponent / 2 : (exponent - 1) / 2;
        var quantum = rootExponent - format.Fraction;
        var numerator = value.Mantissa;
        var denominator = BigInteger.One;
        Scale(ref numerator, ref denominator, value.Exponent - 2 * quantum);
        var floor = IntegerSqrt(numerator / denominator);
        var inexact = floor * floor * denominator != numerator;
        var comparison = (4 * numerator).CompareTo(denominator * BigInteger.Pow(2 * floor + 1, 2));
        var increment = rounding switch
        {
            FloatRounding.TiesEven => comparison > 0 || (comparison == 0 && !floor.IsEven),
            FloatRounding.TiesAway => comparison >= 0,
            FloatRounding.PlusInfinity => inexact,
            FloatRounding.MinusInfinity or FloatRounding.TowardZero => false,
            _ => throw new InvalidOperationException("Unresolved rounding mode")
        };
        if (increment) floor++;
        return Round(architecture, format, false, floor, BigInteger.One, quantum,
            FloatRounding.TowardZero, control, flags | (inexact ? Inexact : 0));
    }

    private static BigInteger IntegerSqrt(BigInteger value)
    {
        if (value <= 1) return value;
        var estimate = BigInteger.One << checked((int)((value.GetBitLength() + 1) / 2));
        while (true)
        {
            var next = (estimate + value / estimate) >> 1;
            if (next >= estimate) return estimate;
            estimate = next;
        }
    }

    private static BigInteger RoundInteger(BigInteger numerator, BigInteger denominator,
        int shift, bool negative, FloatRounding rounding, out bool inexact)
    {
        Scale(ref numerator, ref denominator, shift);
        var integer = BigInteger.DivRem(numerator, denominator, out var remainder);
        inexact = !remainder.IsZero;
        var comparison = (remainder << 1).CompareTo(denominator);
        var increment = rounding switch
        {
            FloatRounding.TiesEven => comparison > 0 || (comparison == 0 && !integer.IsEven),
            FloatRounding.TiesAway => comparison >= 0,
            FloatRounding.PlusInfinity => inexact && !negative,
            FloatRounding.MinusInfinity => inexact && negative,
            FloatRounding.TowardZero => false,
            _ => throw new InvalidOperationException("Unresolved rounding mode")
        };
        return increment ? integer + 1 : integer;
    }

    private static int FloorLog2(BigInteger numerator, BigInteger denominator)
    {
        var candidate = checked((int)(numerator.GetBitLength() - denominator.GetBitLength()));
        var comparison = candidate >= 0 ? numerator.CompareTo(denominator << candidate)
            : (numerator << -candidate).CompareTo(denominator);
        return comparison < 0 ? candidate - 1 : candidate;
    }

    private static void Scale(ref BigInteger numerator, ref BigInteger denominator, int shift)
    {
        if (shift >= 0) numerator <<= shift;
        else denominator <<= -shift;
    }

    private static Number Unpack(Architecture architecture, Format format, BigInteger value,
        uint control, ref uint flags)
    {
        var bits = (ulong)(value & Mask(format.Width));
        var negative = (bits & format.Sign) != 0;
        var fraction = bits & format.FractionMask;
        var exponent = (int)((bits & ~format.Sign) >> format.Fraction);
        var special = exponent == 2 * format.Bias + 1;
        var denormal = exponent == 0 && fraction != 0;
        var flush = architecture == Architecture.Arm64
            ? (control & (1U << 24)) != 0 : (control & (1U << 6)) != 0;
        if (denormal && flush)
        {
            if (architecture == Architecture.Arm64) flags |= InputDenormal;
            return new(Signed(0, negative, format), negative, BigInteger.Zero,
                format.Minimum - format.Fraction, false, false, false, false);
        }
        var mantissa = new BigInteger(fraction);
        if (exponent != 0 && !special) mantissa |= BigInteger.One << format.Fraction;
        return new(bits, negative, mantissa,
            (exponent == 0 ? format.Minimum : exponent - format.Bias) - format.Fraction,
            special && fraction == 0, special && fraction != 0,
            special && fraction != 0 && (fraction & format.Quiet) == 0, denormal);
    }

    private static int Compare(Number left, Number right)
    {
        if (left.Zero && right.Zero) return 0;
        if (left.Negative != right.Negative) return left.Negative ? -1 : 1;
        int magnitude;
        if (left.Infinity || right.Infinity) magnitude = left.Infinity.CompareTo(right.Infinity);
        else
        {
            var exponent = Math.Min(left.Exponent, right.Exponent);
            magnitude = (left.Mantissa << (left.Exponent - exponent))
                .CompareTo(right.Mantissa << (right.Exponent - exponent));
        }
        return left.Negative ? -magnitude : magnitude;
    }

    private static uint DenormalFlags(Architecture architecture, Number left, Number right) =>
        architecture == Architecture.X64 && (left.Denormal || right.Denormal) ? InputDenormal : 0;

    internal static bool ValidFractionBits(Architecture architecture, FloatOperation spec)
    {
        if (spec.FractionBits == 0) return true;
        if (architecture != Architecture.Arm64 || spec.FractionBits < 0) return false;
        return spec.Kind switch
        {
            FloatKind.FromSigned or FloatKind.FromUnsigned => spec.FractionBits <= spec.OperandWidth && spec.Rounding == FloatRounding.Current,
            FloatKind.ToSigned or FloatKind.ToUnsigned => spec.FractionBits <= spec.ResultWidth && spec.Rounding == FloatRounding.TowardZero,
            _ => false
        };
    }

    private static FloatRounding ResolveRounding(Architecture architecture, FloatRounding rounding, uint control)
    {
        if (rounding != FloatRounding.Current) return rounding;
        var mode = (control >> (architecture == Architecture.Arm64 ? 22 : 13)) & 3;
        return mode switch
        {
            0 => FloatRounding.TiesEven,
            1 => architecture == Architecture.Arm64 ? FloatRounding.PlusInfinity : FloatRounding.MinusInfinity,
            2 => architecture == Architecture.Arm64 ? FloatRounding.MinusInfinity : FloatRounding.PlusInfinity,
            _ => FloatRounding.TowardZero
        };
    }

    private static Format GetFormat(int width) => width switch
    {
        32 => new(32, 23, 127),
        64 => new(64, 52, 1023),
        _ => throw new InvalidOperationException($"Unsupported floating width {width}")
    };

    private static ulong Signed(ulong bits, bool negative, Format format) => bits | (negative ? format.Sign : 0);
    private static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
    private static bool TestBit(this BigInteger value, int bit) => (value & (BigInteger.One << bit)) != 0;
}
