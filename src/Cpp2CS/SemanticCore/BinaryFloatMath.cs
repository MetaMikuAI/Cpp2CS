using System.Numerics;

namespace Cpp2CS.SemanticCore;

// 有限值使用精确整数与二进制指数；除法仅在最终舍入时截断。
public static class BinaryFloatMath
{
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

    public static BinaryFloatResult Evaluate(BinaryFloatSpec spec, params BigInteger[] operands)
    {
        var error = spec.Validate();
        if (error is not null) throw new ArgumentException(error, nameof(spec));
        if (operands.Length != spec.InputCount) throw new ArgumentException("浮点操作输入数量不匹配", nameof(operands));
        if (operands.Any(x => x.Sign < 0 || x > Mask(spec.OperandWidth))) throw new ArgumentException("浮点输入超出声明宽度", nameof(operands));
        var rules = spec.Rules;
        var rounding = spec.Rounding;
        if (spec.Kind is BinaryFloatKind.FromSigned or BinaryFloatKind.FromUnsigned)
        {
            var integer = spec.Kind == BinaryFloatKind.FromSigned ? BitVectorMath.Signed(operands[0], spec.OperandWidth) : operands[0];
            return Round(GetFormat(spec.ResultWidth), integer.Sign < 0, BigInteger.Abs(integer), BigInteger.One,
                -spec.FractionBits, rounding, rules, 0);
        }
        var input = GetFormat(spec.OperandWidth);
        BinaryFloatException flags = 0;
        var values = new Number[operands.Length];
        for (var i = 0; i < values.Length; i++) values[i] = Unpack(input, operands[i], rules, ref flags);
        var left = values[0];
        var right = values.Length > 1 ? values[1] : default;
        if (spec.Kind is BinaryFloatKind.ToSigned or BinaryFloatKind.ToUnsigned)
            return ToInteger(spec, left, flags);
        if (spec.Kind is BinaryFloatKind.Compare or BinaryFloatKind.CompareSignal)
        {
            if (left.NaN || right.NaN)
                return new(3, flags | (left.Signaling || right.Signaling || spec.Kind == BinaryFloatKind.CompareSignal ? BinaryFloatException.Invalid : 0));
            var order = Compare(left, right);
            return new(order < 0 ? 1 : order > 0 ? 2 : 0, flags | DenormalFlags(rules, values));
        }
        if (spec.Kind is BinaryFloatKind.Minimum or BinaryFloatKind.Maximum or BinaryFloatKind.MinimumNumber or
            BinaryFloatKind.MaximumNumber or BinaryFloatKind.MinimumSecond or BinaryFloatKind.MaximumSecond)
            return MinMax(spec, input, values, flags);
        var output = GetFormat(spec.ResultWidth);
        if (values.Any(x => x.NaN)) return Postprocess(spec.Kind, output, PropagateNaN(input, output, values, rules, flags));
        if (spec.InputCount == 3) return Fused(spec, output, values, flags);
        if (spec.Kind == BinaryFloatKind.Convert)
        {
            flags |= DenormalFlags(rules, values);
            if (left.Infinity) return new(Signed(output.Infinity, left.Negative, output), flags);
            return Round(output, left.Negative, left.Mantissa, BigInteger.One, left.Exponent, rounding, rules, flags);
        }
        if (spec.Kind is BinaryFloatKind.RoundIntegral or BinaryFloatKind.RoundIntegralExact)
        {
            if (left.Infinity || left.Zero) return new(left.Bits, flags);
            var integer = RoundInteger(left.Mantissa, BigInteger.One, left.Exponent, left.Negative, rounding, out var inexact);
            if (inexact && spec.Kind == BinaryFloatKind.RoundIntegralExact) flags |= BinaryFloatException.Inexact;
            return Round(output, left.Negative, integer, BigInteger.One, 0, BinaryFloatRounding.TowardZero, rules, flags);
        }
        if (spec.Kind == BinaryFloatKind.Sqrt)
        {
            if (left.Zero) return new(left.Bits, flags);
            if (left.Negative) return InvalidResult(output, rules, flags);
            flags |= DenormalFlags(rules, values);
            return left.Infinity ? new(output.Infinity, flags) : SquareRoot(output, left, rounding, rules, flags);
        }
        var sign = left.Negative ^ right.Negative;
        BinaryFloatResult result;
        switch (spec.Kind)
        {
            case BinaryFloatKind.Add:
            case BinaryFloatKind.Sub:
            case BinaryFloatKind.AbsDiff:
            {
                var rightSign = right.Negative ^ (spec.Kind != BinaryFloatKind.Add);
                if (left.Infinity && right.Infinity && left.Negative != rightSign)
                    result = InvalidResult(output, rules, flags);
                else
                {
                    flags |= DenormalFlags(rules, values);
                    if (left.Infinity || right.Infinity)
                        result = new(Signed(output.Infinity, left.Infinity ? left.Negative : rightSign, output), flags);
                    else
                    {
                        var exponent = Math.Min(left.Exponent, right.Exponent);
                        var l = left.Mantissa << (left.Exponent - exponent);
                        var r = right.Mantissa << (right.Exponent - exponent);
                        var sum = (left.Negative ? -l : l) + (rightSign ? -r : r);
                        var negative = sum.Sign < 0 || sum.IsZero &&
                            (left.Zero && right.Zero && left.Negative == rightSign ? left.Negative : rounding == BinaryFloatRounding.MinusInfinity);
                        result = Round(output, negative, BigInteger.Abs(sum), BigInteger.One, exponent, rounding, rules, flags);
                    }
                }
                break;
            }
            case BinaryFloatKind.Mul:
            case BinaryFloatKind.NegMul:
                if (left.Infinity && right.Zero || right.Infinity && left.Zero) result = InvalidResult(output, rules, flags);
                else
                {
                    flags |= DenormalFlags(rules, values);
                    result = left.Infinity || right.Infinity ? new(Signed(output.Infinity, sign, output), flags) :
                        Round(output, sign, left.Mantissa * right.Mantissa, BigInteger.One, left.Exponent + right.Exponent, rounding, rules, flags);
                }
                break;
            case BinaryFloatKind.Div:
                if (left.Infinity && right.Infinity || left.Zero && right.Zero) result = InvalidResult(output, rules, flags);
                else if (right.Zero && !left.Infinity) result = new(Signed(output.Infinity, sign, output), flags | BinaryFloatException.DivideByZero);
                else
                {
                    flags |= DenormalFlags(rules, values);
                    result = left.Infinity ? new(Signed(output.Infinity, sign, output), flags) :
                        left.Zero || right.Infinity ? new(Signed(0, sign, output), flags) :
                        Round(output, sign, left.Mantissa, right.Mantissa, left.Exponent - right.Exponent, rounding, rules, flags);
                }
                break;
            default: throw new InvalidOperationException($"未实现的浮点运算 {spec.Kind}");
        }
        return Postprocess(spec.Kind, output, result);
    }

    private static BinaryFloatResult Postprocess(BinaryFloatKind kind, Format format, BinaryFloatResult result) => kind switch
    {
        BinaryFloatKind.NegMul => result with { Bits = result.Bits ^ format.Sign },
        BinaryFloatKind.AbsDiff => result with { Bits = result.Bits & (format.Sign - 1) },
        _ => result
    };
    private static BinaryFloatResult Fused(BinaryFloatSpec spec, Format format, Number[] values, BinaryFloatException flags)
    {
        var left = values[0]; var right = values[1]; var addend = values[2];
        if (left.Infinity && right.Zero || right.Infinity && left.Zero) return InvalidResult(format, spec.Rules, flags);
        var pn = left.Negative ^ right.Negative ^ (spec.Kind is BinaryFloatKind.NegMulAdd or BinaryFloatKind.NegMulSub);
        var an = addend.Negative ^ (spec.Kind is BinaryFloatKind.MulSub or BinaryFloatKind.NegMulSub);
        var pi = left.Infinity || right.Infinity;
        if (pi && addend.Infinity && pn != an) return InvalidResult(format, spec.Rules, flags);
        flags |= DenormalFlags(spec.Rules, values);
        if (pi || addend.Infinity) return new(Signed(format.Infinity, pi ? pn : an, format), flags);
        var product = left.Mantissa * right.Mantissa;
        var pe = left.Exponent + right.Exponent;
        var exponent = Math.Min(pe, addend.Exponent);
        var p = product << (pe - exponent);
        var a = addend.Mantissa << (addend.Exponent - exponent);
        var sum = (pn ? -p : p) + (an ? -a : a);
        var negative = sum.Sign < 0 || sum.IsZero &&
            (product.IsZero && addend.Zero && pn == an ? pn : spec.Rounding == BinaryFloatRounding.MinusInfinity);
        return Round(format, negative, BigInteger.Abs(sum), BigInteger.One, exponent, spec.Rounding, spec.Rules, flags);
    }
    private static BinaryFloatResult MinMax(BinaryFloatSpec spec, Format format, Number[] values, BinaryFloatException flags)
    {
        var left = values[0]; var right = values[1];
        var minimum = spec.Kind is BinaryFloatKind.Minimum or BinaryFloatKind.MinimumNumber or BinaryFloatKind.MinimumSecond;
        if (spec.Kind is BinaryFloatKind.MinimumSecond or BinaryFloatKind.MaximumSecond)
        {
            if (left.NaN || right.NaN) return new(right.Bits, flags | BinaryFloatException.Invalid);
            var order = Compare(left, right);
            return new((minimum ? order < 0 : order > 0) ? left.Bits : right.Bits, flags | DenormalFlags(spec.Rules, values));
        }
        if (spec.Kind is BinaryFloatKind.MinimumNumber or BinaryFloatKind.MaximumNumber)
        {
            if (left.NaN && !left.Signaling && !right.NaN) return new(right.Bits, flags);
            if (right.NaN && !right.Signaling && !left.NaN) return new(left.Bits, flags);
        }
        if (left.NaN || right.NaN) return PropagateNaN(format, format, values, spec.Rules, flags);
        flags |= DenormalFlags(spec.Rules, values);
        if (left.Zero && right.Zero) return new(Signed(0, minimum ? left.Negative || right.Negative : left.Negative && right.Negative, format), flags);
        var comparison = Compare(left, right);
        return new((minimum ? comparison < 0 : comparison > 0) ? left.Bits : right.Bits, flags);
    }
    private static BinaryFloatResult ToInteger(BinaryFloatSpec spec, Number value, BinaryFloatException flags)
    {
        var unsigned = spec.Kind == BinaryFloatKind.ToUnsigned;
        var minimum = unsigned ? BigInteger.Zero : -(BigInteger.One << (spec.ResultWidth - 1));
        var maximum = (BigInteger.One << (spec.ResultWidth - (unsigned ? 0 : 1))) - 1;
        BigInteger InvalidInteger(BigInteger candidate) => spec.Rules.InvalidInteger switch
        {
            BinaryInvalidInteger.Saturate => value.NaN ? BigInteger.Zero : BigInteger.Clamp(candidate, minimum, maximum),
            BinaryInvalidInteger.Minimum => minimum,
            BinaryInvalidInteger.Zero => BigInteger.Zero,
            _ => throw new InvalidOperationException()
        };
        if (value.NaN || value.Infinity)
            return new(InvalidInteger(value.Negative ? minimum : maximum) & Mask(spec.ResultWidth), flags | BinaryFloatException.Invalid);
        var integer = RoundInteger(value.Mantissa, BigInteger.One, value.Exponent + spec.FractionBits, value.Negative, spec.Rounding, out var inexact);
        if (value.Negative) integer = -integer;
        if (integer < minimum || integer > maximum)
            return new(InvalidInteger(integer) & Mask(spec.ResultWidth), flags | BinaryFloatException.Invalid);
        return new(integer & Mask(spec.ResultWidth), flags | (inexact ? BinaryFloatException.Inexact : 0));
    }
    private static BinaryFloatResult PropagateNaN(Format input, Format output, Number[] values, BinaryFloatRules rules, BinaryFloatException flags)
    {
        if (values.Any(x => x.Signaling)) flags |= BinaryFloatException.Invalid;
        if (rules.NaN == BinaryNaNRule.Canonical) return new(output.Infinity | output.Quiet, flags);
        var source = rules.NaN == BinaryNaNRule.FirstSignalingThenFirst && values.Any(x => x.Signaling)
            ? values.First(x => x.Signaling) : values.First(x => x.NaN);
        var payload = new BigInteger(source.Bits & input.FractionMask);
        payload = output.Fraction >= input.Fraction ? payload << (output.Fraction - input.Fraction) : payload >> (input.Fraction - output.Fraction);
        return new(Signed(output.Infinity | output.Quiet | (ulong)payload, source.Negative, output), flags);
    }
    private static BinaryFloatResult InvalidResult(Format format, BinaryFloatRules rules, BinaryFloatException flags) =>
        new(Signed(format.Infinity | format.Quiet, rules.InvalidNaNNegative, format), flags | BinaryFloatException.Invalid);

    private static BinaryFloatResult Round(Format format, bool negative, BigInteger numerator, BigInteger denominator,
        int exponent, BinaryFloatRounding rounding, BinaryFloatRules rules, BinaryFloatException flags)
    {
        if (numerator.IsZero) return new(Signed(0, negative, format), flags);
        var binaryExponent = FloorLog2(numerator, denominator) + exponent;
        var tinyBefore = binaryExponent < format.Minimum;
        if (tinyBefore && rules.SubnormalOutput == BinarySubnormalOutput.SignedZeroBeforeRounding)
            return new(Signed(0, negative, format), flags | BinaryFloatException.Underflow | (rules.FlushRaisesInexact ? BinaryFloatException.Inexact : 0));
        var unconstrained = RoundInteger(numerator, denominator, exponent - binaryExponent + format.Fraction, negative, rounding, out _);
        var roundedExponent = binaryExponent + (unconstrained >= (BigInteger.One << (format.Fraction + 1)) ? 1 : 0);
        if (roundedExponent > format.Maximum)
        {
            var infinity = rounding is BinaryFloatRounding.TiesEven or BinaryFloatRounding.TiesAway ||
                rounding == BinaryFloatRounding.PlusInfinity && !negative || rounding == BinaryFloatRounding.MinusInfinity && negative;
            return new(Signed(infinity ? format.Infinity : format.Infinity - 1, negative, format), flags | BinaryFloatException.Overflow | BinaryFloatException.Inexact);
        }
        var tiny = rules.Tininess == BinaryTininess.BeforeRounding ? tinyBefore : roundedExponent < format.Minimum;
        if (roundedExponent < format.Minimum && rules.SubnormalOutput == BinarySubnormalOutput.SignedZeroAfterRounding)
            return new(Signed(0, negative, format), flags | BinaryFloatException.Underflow | (rules.FlushRaisesInexact ? BinaryFloatException.Inexact : 0));
        var quantum = Math.Max(binaryExponent, format.Minimum) - format.Fraction;
        var mantissa = RoundInteger(numerator, denominator, exponent - quantum, negative, rounding, out var inexact);
        if (inexact) flags |= BinaryFloatException.Inexact;
        if (tiny && (inexact || rules.ExactTinyUnderflow)) flags |= BinaryFloatException.Underflow;
        if (mantissa.IsZero) return new(Signed(0, negative, format), flags);
        var resultExponent = Math.Max(binaryExponent, format.Minimum);
        if (mantissa >= (BigInteger.One << (format.Fraction + 1))) { mantissa >>= 1; resultExponent++; }
        var encodedExponent = mantissa < (BigInteger.One << format.Fraction) ? 0 : resultExponent + format.Bias;
        return new(Signed(((ulong)encodedExponent << format.Fraction) | ((ulong)mantissa & format.FractionMask), negative, format), flags);
    }
    private static BinaryFloatResult SquareRoot(Format format, Number value, BinaryFloatRounding rounding, BinaryFloatRules rules, BinaryFloatException flags)
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
            BinaryFloatRounding.TiesEven => comparison > 0 || comparison == 0 && !floor.IsEven,
            BinaryFloatRounding.TiesAway => comparison >= 0,
            BinaryFloatRounding.PlusInfinity => inexact,
            BinaryFloatRounding.MinusInfinity or BinaryFloatRounding.TowardZero => false,
            _ => throw new InvalidOperationException()
        };
        if (increment) floor++;
        return Round(format, false, floor, BigInteger.One, quantum, BinaryFloatRounding.TowardZero, rules,
            flags | (inexact ? BinaryFloatException.Inexact : 0));
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
    private static BigInteger RoundInteger(BigInteger numerator, BigInteger denominator, int shift, bool negative,
        BinaryFloatRounding rounding, out bool inexact)
    {
        Scale(ref numerator, ref denominator, shift);
        var integer = BigInteger.DivRem(numerator, denominator, out var remainder);
        inexact = !remainder.IsZero;
        var comparison = (remainder << 1).CompareTo(denominator);
        var increment = rounding switch
        {
            BinaryFloatRounding.TiesEven => comparison > 0 || comparison == 0 && !integer.IsEven,
            BinaryFloatRounding.TiesAway => comparison >= 0,
            BinaryFloatRounding.PlusInfinity => inexact && !negative,
            BinaryFloatRounding.MinusInfinity => inexact && negative,
            BinaryFloatRounding.TowardZero => false,
            _ => throw new InvalidOperationException()
        };
        return increment ? integer + 1 : integer;
    }
    private static int FloorLog2(BigInteger numerator, BigInteger denominator)
    {
        var candidate = checked((int)(numerator.GetBitLength() - denominator.GetBitLength()));
        var comparison = candidate >= 0 ? numerator.CompareTo(denominator << candidate) : (numerator << -candidate).CompareTo(denominator);
        return comparison < 0 ? candidate - 1 : candidate;
    }
    private static void Scale(ref BigInteger numerator, ref BigInteger denominator, int shift)
    {
        if (shift >= 0) numerator <<= shift;
        else denominator <<= -shift;
    }
    private static Number Unpack(Format format, BigInteger value, BinaryFloatRules rules, ref BinaryFloatException flags)
    {
        var bits = (ulong)value;
        var negative = (bits & format.Sign) != 0;
        var fraction = bits & format.FractionMask;
        var exponent = (int)((bits & ~format.Sign) >> format.Fraction);
        var special = exponent == 2 * format.Bias + 1;
        var denormal = exponent == 0 && fraction != 0;
        if (denormal && rules.SubnormalInput == BinarySubnormalInput.SignedZero)
        {
            if (rules.DenormalException == BinaryDenormalException.WhenFlushed) flags |= BinaryFloatException.InputDenormal;
            return new(Signed(0, negative, format), negative, BigInteger.Zero, format.Minimum - format.Fraction, false, false, false, false);
        }
        var mantissa = new BigInteger(fraction);
        if (exponent != 0 && !special) mantissa |= BigInteger.One << format.Fraction;
        return new(bits, negative, mantissa, (exponent == 0 ? format.Minimum : exponent - format.Bias) - format.Fraction,
            special && fraction == 0, special && fraction != 0, special && fraction != 0 && (fraction & format.Quiet) == 0, denormal);
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
            magnitude = (left.Mantissa << (left.Exponent - exponent)).CompareTo(right.Mantissa << (right.Exponent - exponent));
        }
        return left.Negative ? -magnitude : magnitude;
    }
    private static BinaryFloatException DenormalFlags(BinaryFloatRules rules, Number[] values) =>
        rules.DenormalException == BinaryDenormalException.OnNumericUse && values.Any(x => x.Denormal) ? BinaryFloatException.InputDenormal : 0;
    private static Format GetFormat(int width) => width switch
    {
        16 => new(16, 10, 15), 32 => new(32, 23, 127), 64 => new(64, 52, 1023),
        _ => throw new InvalidOperationException("浮点格式无效")
    };
    private static ulong Signed(ulong bits, bool negative, Format format) => bits | (negative ? format.Sign : 0);
    private static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
}
