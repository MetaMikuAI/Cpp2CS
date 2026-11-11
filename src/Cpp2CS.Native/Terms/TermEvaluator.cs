using System.Numerics;

namespace Cpp2CS.Native.Terms;

/// <summary>Undefined 包括部分位未定义；具体范围由 DefinedMask 给出。</summary>
public enum EvaluationStatus { Defined, Undefined, Unsupported }

/// <summary>位型结果；不支持与语义未定义分开，调用方不能把不支持当作证明。</summary>
public readonly record struct EvaluationResult(EvaluationStatus Status, BigInteger Bits, string? Reason = null, BigInteger DefinedMask = default)
{
    // 独立运算尚无位宽上下文，-1 表示全定义；Evaluate 返回时裁成项的位宽。
    public static EvaluationResult Defined(BigInteger bits) => new(EvaluationStatus.Defined, bits, DefinedMask: -1);
    public static EvaluationResult Partial(BigInteger bits, BigInteger mask, int width) =>
        new(mask == TermEvaluator.Mask(width) ? EvaluationStatus.Defined : EvaluationStatus.Undefined,
            bits & mask, DefinedMask: mask);
    public static EvaluationResult Undefined => new(EvaluationStatus.Undefined, 0);
    public static EvaluationResult Unsupported(string why) => new(EvaluationStatus.Unsupported, 0, why);
}

public sealed class TermEvaluator(Func<AtomIdentity, BigInteger> atoms,
    Func<Operator, int, IReadOnlyList<BigInteger>, EvaluationResult>? interpret = null,
    Func<UnknownIdentity, BigInteger>? unknowns = null)
{
    public EvaluationResult Evaluate(Term term)
    {
        var cache = new Dictionary<Term, EvaluationResult>();
        EvaluationResult Visit(Term t)
        {
            if (cache.TryGetValue(t, out var known)) return known;
            var result = Compute(t);
            result = result with { DefinedMask = result.DefinedMask & Mask(t.Width) };
            cache.Add(t, result);
            return result;
        }
        EvaluationResult Compute(Term t)
        {
            if (t.Kind == TermKind.Constant) return EvaluationResult.Defined(t.ConstantValue!.Value);
            if (t.Kind == TermKind.Undefined) return EvaluationResult.Undefined;
            if (t.Kind == TermKind.Unknown)
            {
                if (unknowns is null) return EvaluationResult.Unsupported("未知身份缺少赋值。");
                var bits = unknowns(((UnknownValue)t.Payload!).Identity);
                if (bits < 0 || bits > Mask(t.Width)) throw new ArgumentOutOfRangeException(nameof(unknowns));
                return EvaluationResult.Defined(bits);
            }
            if (t.Kind == TermKind.Atom)
            {
                var bits = atoms(t.Identity!);
                if (bits < 0 || bits > Mask(t.Width)) throw new ArgumentOutOfRangeException(nameof(atoms));
                return EvaluationResult.Defined(bits);
            }
            if (t.Operator is CoreOperator { Operation: CoreOperation.Select })
            {
                var condition = Visit(t.Operands[0]);
                return condition.Status == EvaluationStatus.Defined ? Visit(t.Operands[condition.Bits.IsZero ? 2 : 1]) : condition.Status == EvaluationStatus.Unsupported ? condition : EvaluationResult.Undefined;
            }
            var values = t.Operands.Select(Visit).ToArray();
            // 不支持不能被另一个操作数的未定义遮住。
            var unsupported = values.FirstOrDefault(v => v.Status == EvaluationStatus.Unsupported);
            if (unsupported.Status == EvaluationStatus.Unsupported) return unsupported;
            var bitsArray = values.Select(v => v.Bits).ToArray();
            if (t.Kind == TermKind.Slice) return EvaluationResult.Partial(bitsArray[0] >> t.SliceLow!.Value,
                (values[0].DefinedMask >> t.SliceLow.Value) & Mask(t.Width), t.Width);
            if (t.Kind == TermKind.Concat)
            {
                BigInteger bits = 0;
                BigInteger mask = 0;
                var offset = 0;
                for (var i = 0; i < values.Length; i++)
                {
                    bits |= bitsArray[i] << offset;
                    mask |= (values[i].DefinedMask & Mask(t.Operands[i].Width)) << offset;
                    offset += t.Operands[i].Width;
                }
                return EvaluationResult.Partial(bits, mask, t.Width);
            }
            if (values.Any(v => v.Status == EvaluationStatus.Undefined)) return EvaluationResult.Undefined;
            if (t.Operator is CoreOperator core) return EvaluateCore(core.Operation, t.Width, t.Operands[0].Width, bitsArray);
            return interpret?.Invoke(t.Operator!, t.Width, bitsArray) ?? EvaluationResult.Unsupported(t.Operator!.Name);
        }
        return Visit(term);
    }

    internal static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
    internal static BigInteger Signed(BigInteger value, int width) => value.TestBit(width - 1) ? value - (BigInteger.One << width) : value;

    internal static EvaluationResult EvaluateCore(CoreOperation op, int width, int inputWidth, IReadOnlyList<BigInteger> v)
    {
        var a = v[0];
        var b = v.Count > 1 ? v[1] : BigInteger.Zero;
        var sa = Signed(a, inputWidth);
        var sb = Signed(b, inputWidth);
        EvaluationResult Value(BigInteger x) => EvaluationResult.Defined(x & Mask(width));
        EvaluationResult Bool(bool x) => Value(x ? 1 : 0);
        if (op is CoreOperation.SignedDivide or CoreOperation.SignedRemainder &&
            (b.IsZero || sa == -(BigInteger.One << (inputWidth - 1)) && sb == -1)) return EvaluationResult.Undefined;
        if (op is CoreOperation.UnsignedDivide or CoreOperation.UnsignedRemainder && b.IsZero) return EvaluationResult.Undefined;
        if (op is CoreOperation.ShiftLeft or CoreOperation.LogicalShiftRight or CoreOperation.ArithmeticShiftRight && b >= width)
            return EvaluationResult.Undefined;
        switch (op)
        {
            case CoreOperation.Add: return Value(a + b);
            case CoreOperation.Subtract: return Value(a - b);
            case CoreOperation.Multiply: return Value(a * b);
            case CoreOperation.SignedDivide: return Value(sa / sb);
            case CoreOperation.UnsignedDivide: return Value(a / b);
            case CoreOperation.SignedRemainder: return Value(sa % sb);
            case CoreOperation.UnsignedRemainder: return Value(a % b);
            case CoreOperation.Negate: return Value(-a);
            case CoreOperation.And: return Value(a & b);
            case CoreOperation.Or: return Value(a | b);
            case CoreOperation.Xor: return Value(a ^ b);
            case CoreOperation.Not: return Value(~a);
            case CoreOperation.ShiftLeft: return Value(a << (int)b);
            case CoreOperation.LogicalShiftRight: return Value(a >> (int)b);
            case CoreOperation.ArithmeticShiftRight: return Value(sa >> (int)b);
            case CoreOperation.RotateRight:
                var shift = (int)(b % width);
                return Value((a >> shift) | (a << (width - shift)));
            case CoreOperation.SignedMultiplyHigh: return Value((sa * sb) >> width);
            case CoreOperation.UnsignedMultiplyHigh: return Value((a * b) >> width);
            case CoreOperation.Equal: return Bool(a == b);
            case CoreOperation.NotEqual: return Bool(a != b);
            case CoreOperation.SignedLess: return Bool(sa < sb);
            case CoreOperation.SignedLessEqual: return Bool(sa <= sb);
            case CoreOperation.UnsignedLess: return Bool(a < b);
            case CoreOperation.UnsignedLessEqual: return Bool(a <= b);
            case CoreOperation.ZeroExtend: case CoreOperation.Truncate: return Value(a);
            case CoreOperation.SignExtend: return Value(sa);
            case CoreOperation.CountLeadingZeros: return Value(inputWidth - a.GetBitLength());
            case CoreOperation.PopulationCount: return Value(BigInteger.PopCount(a));
            case CoreOperation.ReverseBits:
                BigInteger reversed = 0;
                for (var i = 0; i < width; i++) reversed = (reversed << 1) | ((a >> i) & 1);
                return Value(reversed);
            case CoreOperation.ReverseBytes:
                BigInteger bytes = 0;
                for (var i = 0; i < width; i += 8) bytes = (bytes << 8) | ((a >> i) & 255);
                return Value(bytes);
            case CoreOperation.Select: return Value(a.IsZero ? v[2] : b);
        }
        return Floating(op, width, inputWidth, v);
    }

    private static EvaluationResult Floating(CoreOperation op, int width, int inputWidth, IReadOnlyList<BigInteger> v)
    {
        var integerInput = op is CoreOperation.SignedToFloat or CoreOperation.UnsignedToFloat;
        var integerOutput = op is CoreOperation.FloatToSigned or CoreOperation.FloatToUnsigned;
        var comparison = op is >= CoreOperation.FloatEqual and <= CoreOperation.FloatUnordered;
        if ((!integerInput && inputWidth is not (32 or 64)) || (!integerOutput && !comparison && width is not (32 or 64)))
            return EvaluationResult.Unsupported("浮点求值仅支持 binary32 与 binary64。");
        double Decode(BigInteger bits) => inputWidth == 32 ? BitConverter.UInt32BitsToSingle((uint)bits) : BitConverter.UInt64BitsToDouble((ulong)bits);
        EvaluationResult Encode(double x)
        {
            if (width == 32) return EvaluationResult.Defined(float.IsNaN((float)x) ? 0x7fc00000U : BitConverter.SingleToUInt32Bits((float)x));
            return EvaluationResult.Defined(double.IsNaN(x) ? 0x7ff8000000000000UL : BitConverter.DoubleToUInt64Bits(x));
        }
        if (integerInput)
        {
            var integer = op == CoreOperation.SignedToFloat ? Signed(v[0], inputWidth) : v[0];
            // 先在整数域取目标有效位并就近取偶，避免 BigInteger 转换的截断和双重舍入。
            var negative = integer.Sign < 0;
            integer = BigInteger.Abs(integer);
            var precision = width == 32 ? 24 : 53;
            var shift = (int)Math.Max(0, integer.GetBitLength() - precision);
            var significand = integer >> shift;
            if (shift > 0)
            {
                var remainder = integer - (significand << shift);
                var half = BigInteger.One << (shift - 1);
                if (remainder > half || remainder == half && !significand.IsEven) significand++;
            }
            var result = Math.ScaleB((double)significand, shift);
            return Encode(negative ? -result : result);
        }
        var a = Decode(v[0]);
        var b = v.Count > 1 ? Decode(v[1]) : 0;
        if (integerOutput)
        {
            if (!double.IsFinite(a)) return EvaluationResult.Undefined;
            var integer = new BigInteger(a);
            var signed = op == CoreOperation.FloatToSigned;
            var min = signed ? -(BigInteger.One << (width - 1)) : BigInteger.Zero;
            var max = (BigInteger.One << (signed ? width - 1 : width)) - 1;
            return integer < min || integer > max ? EvaluationResult.Undefined : EvaluationResult.Defined(integer & Mask(width));
        }
        if (op is CoreOperation.FloatNegate or CoreOperation.FloatAbs)
            return EvaluationResult.Defined(op == CoreOperation.FloatNegate ? v[0] ^ (BigInteger.One << (width - 1)) : v[0] & Mask(width - 1));
        if (comparison)
        {
            var predicate = op switch
            {
                CoreOperation.FloatEqual => a == b,
                CoreOperation.FloatNotEqual => a != b,
                CoreOperation.FloatLess => a < b,
                CoreOperation.FloatLessEqual => a <= b,
                CoreOperation.FloatOrdered => !double.IsNaN(a) && !double.IsNaN(b),
                _ => double.IsNaN(a) || double.IsNaN(b)
            };
            return EvaluationResult.Defined(predicate ? 1 : 0);
        }
        if (op is >= CoreOperation.FloatMinimum and <= CoreOperation.FloatMaximumNumber)
        {
            var number = op is CoreOperation.FloatMinimumNumber or CoreOperation.FloatMaximumNumber;
            if (double.IsNaN(a) || double.IsNaN(b)) return Encode(number ? (double.IsNaN(a) ? b : a) : double.NaN);
            var minimum = op is CoreOperation.FloatMinimum or CoreOperation.FloatMinimumNumber;
            if (a == 0 && b == 0)
            {
                var signA = v[0].TestBit(inputWidth - 1);
                var signB = v[1].TestBit(inputWidth - 1);
                return EvaluationResult.Defined((minimum ? signA || signB : signA && signB) ? BigInteger.One << (width - 1) : 0);
            }
            return Encode(minimum ? Math.Min(a, b) : Math.Max(a, b));
        }
        // 单精度算术必须直接在 float 上执行；FMA 只舍入一次。
        if (width == 32)
        {
            var x = (float)a; var y = (float)b;
            return Encode(op switch
            {
                CoreOperation.FloatAdd => x + y, CoreOperation.FloatSubtract => x - y,
                CoreOperation.FloatMultiply => x * y, CoreOperation.FloatDivide => x / y,
                CoreOperation.FloatRemainder => MathF.IEEERemainder(x, y), CoreOperation.FloatSqrt => MathF.Sqrt(x),
                CoreOperation.FloatFloor => MathF.Floor(x), CoreOperation.FloatCeiling => MathF.Ceiling(x),
                CoreOperation.FloatTruncate => MathF.Truncate(x), CoreOperation.FloatRoundToEven => MathF.Round(x),
                CoreOperation.FloatFusedMultiplyAdd => MathF.FusedMultiplyAdd(x, y, (float)Decode(v[2])),
                CoreOperation.FloatConvert => (float)a,
                _ => throw new InvalidOperationException($"未实现核心运算 {op}。")
            });
        }
        return Encode(op switch
        {
            CoreOperation.FloatAdd => a + b, CoreOperation.FloatSubtract => a - b,
            CoreOperation.FloatMultiply => a * b, CoreOperation.FloatDivide => a / b,
            CoreOperation.FloatRemainder => Math.IEEERemainder(a, b), CoreOperation.FloatSqrt => Math.Sqrt(a),
            CoreOperation.FloatFloor => Math.Floor(a), CoreOperation.FloatCeiling => Math.Ceiling(a),
            CoreOperation.FloatTruncate => Math.Truncate(a), CoreOperation.FloatRoundToEven => Math.Round(a),
            CoreOperation.FloatFusedMultiplyAdd => Math.FusedMultiplyAdd(a, b, Decode(v[2])), CoreOperation.FloatConvert => a,
            _ => throw new InvalidOperationException($"未实现核心运算 {op}。")
        });
    }

    /// <summary>精化保留原结果的每个有定义位；不支持不能充当证明。</summary>
    public static bool Refines(EvaluationResult before, EvaluationResult after, int width)
    {
        if (before.Status == EvaluationStatus.Unsupported || after.Status == EvaluationStatus.Unsupported) return false;
        var required = before.DefinedMask & Mask(width);
        return (after.DefinedMask & required) == required && ((before.Bits ^ after.Bits) & required).IsZero;
    }

    /// <summary>浮点结果比较允许任意 NaN；整数和被按位观察的结果使用精确位型比较。</summary>
    public static bool Equivalent(EvaluationResult a, EvaluationResult b, int width, bool floating = false)
    {
        if (a.Status != b.Status) return false;
        if (a.Status == EvaluationStatus.Unsupported) return false;
        if ((a.DefinedMask & Mask(width)) != (b.DefinedMask & Mask(width))) return false;
        if (a.Status == EvaluationStatus.Undefined) return ((a.Bits ^ b.Bits) & a.DefinedMask & Mask(width)).IsZero;
        if (a.Bits == b.Bits) return true;
        bool NaN(BigInteger bits) => width switch
        {
            32 => (bits & 0x7f800000) == 0x7f800000 && (bits & 0x7fffff) != 0,
            64 => (bits & 0x7ff0000000000000UL) == 0x7ff0000000000000UL && (bits & 0xfffffffffffffUL) != 0,
            _ => false
        };
        return floating && NaN(a.Bits) && NaN(b.Bits);
    }
}

internal static class IntegerBits
{
    internal static bool TestBit(this BigInteger value, int bit) => !((value >> bit) & 1).IsZero;
}
