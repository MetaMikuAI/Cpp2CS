using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native.Terms;
using static Cpp2CS.Native.Terms.CoreOperation;

namespace Cpp2CS.Tests;

internal static class TermEvaluatorChecks
{
    public const string Command = "term-evaluator";
    private const int Seed = 41018;
    private sealed record Named : AtomIdentity { public override string StableText => "test.value"; }
    private sealed record Extension : Operator
    {
        public override string Name => "test.extension";
        public override bool Accepts(int resultWidth, ImmutableArray<int> operandWidths) => operandWidths.SequenceEqual([resultWidth]);
    }
    private static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
    private static BigInteger Signed(BigInteger bits, int width) => bits < (BigInteger.One << (width - 1)) ? bits : bits - (BigInteger.One << width);
    public static int Run()
    {
        var a = new Assertions(); var random = new Random(Seed); var covered = new HashSet<CoreOperation>();
        foreach (var op in Enum.GetValues<CoreOperation>())
        {
            if (op.ToString().StartsWith("Float", StringComparison.Ordinal) || op is SignedToFloat or UnsignedToFloat) continue;
            foreach (var width in new[] { 1, 8, 16, 32, 64, 65, 128 })
            {
                if (op == ReverseBytes && width % 8 != 0) continue;
                for (var i = 0; i < 120; i++)
                {
                    var x = TermNormalizationChecks.RandomBits(random, width, i);
                    var y = TermNormalizationChecks.RandomBits(random, width, i / 13);
                    var resultWidth = op is >= Equal and <= UnsignedLessEqual ? 1 : op is ZeroExtend or SignExtend ? width + 9 : op == Truncate ? Math.Max(1, width - 1) : width;
                    if (op == Truncate && width == 1) continue;
                    var arity = op is Negate or Not or ZeroExtend or SignExtend or Truncate or CountLeadingZeros or PopulationCount or ReverseBits or ReverseBytes ? 1 : 2;
                    var table = new TermTable(false);
                    var operands = arity == 1 ? new[] { table.Constant(x, width) } : new[] { table.Constant(x, width), table.Constant(y, width) };
                    if (op == Select) operands = [table.Constant(i % 2, 1), table.Constant(x, width), table.Constant(y, width)];
                    var t = table.Apply(new CoreOperator(op), resultWidth, operands);
                    var actual = new TermEvaluator(_ => throw new InvalidOperationException()).Evaluate(t);
                    var expected = ReferenceInteger(op, width, resultWidth, x, y, i % 2);
                    a.True(TermEvaluator.Equivalent(actual, expected, resultWidth), $"seed={Seed} {op}/{width}/{i} x={x:x} y={y:x} expected={expected} actual={actual}");
                    covered.Add(op);
                }
            }
        }
        CheckFloating<float>(a, random, 32, covered);
        CheckFloating<double>(a, random, 64, covered);
        Boundaries(a);
        foreach (var op in Enum.GetValues<CoreOperation>()) a.True(covered.Contains(op), $"核心运算遗漏 {op}");
        return a.Finish("项求值器");
    }
    private static EvaluationResult ReferenceInteger(CoreOperation op, int width, int resultWidth, BigInteger x, BigInteger y, int condition)
    {
        var sx = Signed(x, width); var sy = Signed(y, width);
        if (op is SignedDivide or SignedRemainder && (sy == 0 || sx == -(BigInteger.One << (width - 1)) && sy == -1) ||
            op is UnsignedDivide or UnsignedRemainder && y == 0 || op is ShiftLeft or LogicalShiftRight or ArithmeticShiftRight && y >= width)
            return EvaluationResult.Undefined;
        BigInteger BitLoop(bool reverseBytes)
        {
            BigInteger result = 0;
            var chunk = reverseBytes ? 8 : 1;
            for (var i = 0; i < width; i += chunk) result += ((x / (BigInteger.One << i)) % (BigInteger.One << chunk)) << (width - i - chunk);
            return result;
        }
        BigInteger Count(bool leading)
        {
            var bits = Enumerable.Range(0, width).Select(i => (x & (BigInteger.One << (width - i - 1))) != 0);
            return leading ? bits.TakeWhile(bit => !bit).Count() : bits.Count(bit => bit);
        }
        var value = op switch
        {
            Add => x + y, Subtract => x - y, Multiply => x * y, Negate => -x,
            SignedDivide => sx / sy, UnsignedDivide => x / y, SignedRemainder => sx % sy, UnsignedRemainder => x % y,
            And => x & y, Or => x | y, Xor => x ^ y, Not => Mask(width) - x,
            ShiftLeft => x * (BigInteger.One << (int)y), LogicalShiftRight => x / (BigInteger.One << (int)y),
            ArithmeticShiftRight => (sx - (sx < 0 ? (BigInteger.One << (int)y) - 1 : 0)) / (BigInteger.One << (int)y),
            RotateRight => ((x % (BigInteger.One << (int)(y % width))) << (width - (int)(y % width))) + (x >> (int)(y % width)),
            SignedMultiplyHigh => ((sx * sy) & Mask(width * 2)) / (BigInteger.One << width), UnsignedMultiplyHigh => x * y / (BigInteger.One << width),
            Equal => x == y ? 1 : 0, NotEqual => x != y ? 1 : 0, SignedLess => sx < sy ? 1 : 0,
            SignedLessEqual => sx <= sy ? 1 : 0, UnsignedLess => x < y ? 1 : 0, UnsignedLessEqual => x <= y ? 1 : 0,
            ZeroExtend or Truncate => x, SignExtend => sx, Select => condition == 1 ? x : y,
            CountLeadingZeros => Count(true), PopulationCount => Count(false), ReverseBits => BitLoop(false), ReverseBytes => BitLoop(true),
            _ => throw new InvalidOperationException(op.ToString())
        };
        return EvaluationResult.Defined(value & Mask(resultWidth));
    }

    private static void CheckFloating<T>(Assertions a, Random random, int width, HashSet<CoreOperation> covered) where T : IFloatingPointIeee754<T>
    {
        BigInteger Bits(T value) => width == 32 ? BitConverter.SingleToUInt32Bits(float.CreateChecked(value)) : BitConverter.DoubleToUInt64Bits(double.CreateChecked(value));
        T FromBits(BigInteger bits) => width == 32 ? T.CreateChecked(BitConverter.UInt32BitsToSingle((uint)bits)) : T.CreateChecked(BitConverter.UInt64BitsToDouble((ulong)bits));
        var special = new[] { T.Zero, T.NegativeZero, T.One, -T.One, T.PositiveInfinity, T.NegativeInfinity, T.NaN, T.Epsilon,
            T.CreateChecked(0.5), T.CreateChecked(-0.5), T.CreateChecked(1.5), T.CreateChecked(2.5) };
        foreach (var op in Enum.GetValues<CoreOperation>().Where(op => op.ToString().StartsWith("Float", StringComparison.Ordinal) || op is SignedToFloat or UnsignedToFloat))
        {
            for (var i = 0; i < 180; i++)
            {
                var x = i < special.Length * 3 ? special[i % special.Length] : FromBits(TermNormalizationChecks.RandomBits(random, width, i));
                var y = i < special.Length * 3 ? special[(i / special.Length + i) % special.Length] : FromBits(TermNormalizationChecks.RandomBits(random, width, i + 1));
                var z = special[(i + 3) % special.Length];
                var table = new TermTable(false);
                var comparison = op is >= FloatEqual and <= FloatUnordered;
                var integerOutput = op is FloatToSigned or FloatToUnsigned;
                var integerInput = op is SignedToFloat or UnsignedToFloat;
                var resultWidth = comparison ? 1 : integerOutput ? 67 : op == FloatConvert ? (width == 32 ? 64 : 32) : width;
                var arity = op is >= FloatAdd and <= FloatRemainder or >= FloatEqual and <= FloatUnordered or >= FloatMinimum and <= FloatMaximumNumber ? 2 : op == FloatFusedMultiplyAdd ? 3 : 1;
                var operands = new[] { table.Constant(Bits(x), width), table.Constant(Bits(y), width), table.Constant(Bits(z), width) }.Take(arity).ToArray();
                // Int64/UInt64 转换由 CLR 直接作为独立参考，不经过 double 中转。
                var integer = TermNormalizationChecks.RandomBits(random, 64, i);
                if (integerInput) operands = [table.Constant(integer, 64)];
                var term = table.Apply(new CoreOperator(op), resultWidth, operands);
                var actual = new TermEvaluator(_ => throw new InvalidOperationException()).Evaluate(term);
                EvaluationResult expected;
                if (integerInput)
                {
                    var signed = Signed(integer, 64);
                    BigInteger bits = width == 32
                        ? BitConverter.SingleToUInt32Bits(op == SignedToFloat ? (float)(long)signed : (float)(ulong)integer)
                        : BitConverter.DoubleToUInt64Bits(op == SignedToFloat ? (double)(long)signed : (double)(ulong)integer);
                    expected = EvaluationResult.Defined(bits);
                }
                else if (integerOutput)
                {
                    var number = double.CreateChecked(x);
                    var truncated = double.IsFinite(number) ? new BigInteger(Math.Truncate(number)) : BigInteger.Zero;
                    var min = op == FloatToSigned ? -(BigInteger.One << 66) : BigInteger.Zero;
                    var max = (BigInteger.One << (op == FloatToSigned ? 66 : 67)) - 1;
                    expected = !double.IsFinite(number) || truncated < min || truncated > max ? EvaluationResult.Undefined : EvaluationResult.Defined(truncated & Mask(67));
                }
                else if (comparison)
                {
                    var predicate = op switch { FloatEqual => x == y, FloatNotEqual => x != y, FloatLess => x < y, FloatLessEqual => x <= y,
                        FloatOrdered => !T.IsNaN(x) && !T.IsNaN(y), _ => T.IsNaN(x) || T.IsNaN(y) };
                    expected = EvaluationResult.Defined(predicate ? 1 : 0);
                }
                else if (op == FloatConvert)
                    expected = EvaluationResult.Defined(resultWidth == 32 ? BitConverter.SingleToUInt32Bits(float.CreateChecked(x)) : BitConverter.DoubleToUInt64Bits(double.CreateChecked(x)));
                else if (op is FloatNegate or FloatAbs)
                    expected = EvaluationResult.Defined(op == FloatNegate ? Bits(x) ^ (BigInteger.One << (width - 1)) : Bits(x) & Mask(width - 1));
                else
                {
                    var value = op switch
                    {
                        FloatAdd => x + y, FloatSubtract => x - y, FloatMultiply => x * y, FloatDivide => x / y,
                        FloatRemainder => T.Ieee754Remainder(x, y), FloatSqrt => T.Sqrt(x), FloatFloor => T.Floor(x), FloatCeiling => T.Ceiling(x),
                        FloatTruncate => T.Truncate(x), FloatRoundToEven => T.Round(x, MidpointRounding.ToEven),
                        FloatMinimum => T.Min(x, y), FloatMaximum => T.Max(x, y), FloatMinimumNumber => T.MinNumber(x, y),
                        FloatMaximumNumber => T.MaxNumber(x, y), FloatFusedMultiplyAdd => T.FusedMultiplyAdd(x, y, z),
                        _ => throw new InvalidOperationException(op.ToString())
                    };
                    expected = EvaluationResult.Defined(Bits(value));
                }
                a.True(TermEvaluator.Equivalent(actual, expected, resultWidth, !comparison && !integerOutput),
                    $"seed={Seed} {op}/{width}/{i} x={Bits(x):x} y={Bits(y):x} z={Bits(z):x} integer={integer:x} expected={expected} actual={actual}");
                covered.Add(op);
            }
        }
    }
    private static void Boundaries(Assertions a)
    {
        var table = new TermTable(false);
        var atom = table.Atom(new Named(), 32);
        var ext = table.Apply(new Extension(), 32, atom);
        a.True(new TermEvaluator(_ => 7).Evaluate(ext).Status == EvaluationStatus.Unsupported, "缺扩展解释器");
        a.True(new TermEvaluator(_ => 7, (_, _, values) => EvaluationResult.Defined(values[0] + 1)).Evaluate(ext).Bits == 8, "扩展解释器");
        foreach (var width in new[] { 16, 128 })
        {
            var value = table.Constant(0, width);
            var t = table.Apply(new CoreOperator(FloatAdd), width, value, value);
            a.True(new TermEvaluator(_ => 0).Evaluate(t).Status == EvaluationStatus.Unsupported, $"明确不支持 binary{width}");
        }
        var unknown = table.Unknown(32, new("test", "未建模"));
        a.True(new TermEvaluator(_ => 0).Evaluate(unknown).Status == EvaluationStatus.Unsupported, "未知缺少身份赋值");
        a.True(new TermEvaluator(_ => 0, unknowns: _ => 19).Evaluate(unknown).Bits == 19, "未知按身份赋值");
        var partial = table.Concat(atom, table.Undefined(32));
        var evaluator = new TermEvaluator(_ => 0x12345678);
        var partialResult = evaluator.Evaluate(partial);
        a.True(partialResult.DefinedMask == uint.MaxValue && partialResult.Bits == 0x12345678, "拼接逐位搬运");
        a.True(evaluator.Evaluate(table.Slice(partial, 0, 32)).Status == EvaluationStatus.Defined, "切片保留有定义位");
        a.True(evaluator.Evaluate(table.Slice(partial, 24, 16)).DefinedMask == 255, "跨界切片掩码");
        a.True(evaluator.Evaluate(table.Apply(new CoreOperator(Add), 64, partial, table.Constant(1, 64))).DefinedMask == 0, "算术读到未定义位整项未定义");
        var conditionUndefined = table.Apply(new CoreOperator(Select), 64, table.Undefined(1), partial, partial);
        a.True(evaluator.Evaluate(conditionUndefined).DefinedMask == 0, "选择未定义条件整项未定义");
        var selectedPartial = table.Apply(new CoreOperator(Select), 64, table.Constant(1, 1), partial, table.Undefined(64));
        a.True(evaluator.Evaluate(selectedPartial).DefinedMask == uint.MaxValue, "选择逐位保留被选分支");
        var unknownId = ((UnknownValue)unknown.Payload!).Identity;
        var assigned = new TermEvaluator(_ => 0, unknowns: id => ReferenceEquals(id, unknownId) ? 19 : 23);
        var otherUnknown = table.Unknown(32, new("test", "未建模"));
        a.True(assigned.Evaluate(table.Apply(new CoreOperator(Subtract), 32, unknown, unknown)).Bits == 0, "同一未知身份取值一致");
        a.True(assigned.Evaluate(otherUnknown).Bits == 23, "同原因不同未知身份可异值");
        var select = table.Apply(new CoreOperator(Select), 32, table.Constant(1, 1), atom, ext);
        a.True(new TermEvaluator(_ => 3).Evaluate(select).Bits == 3, "选择不求未选分支");
        foreach (var bits in new uint[] { 0x7fa12345, 0xffa12345, 0x80000000 })
        {
            var t = table.Apply(new CoreOperator(FloatNegate), 32, table.Constant(bits, 32));
            a.True(new TermEvaluator(_ => 0).Evaluate(t).Bits == (bits ^ 0x80000000U), "取负保留载荷");
        }
        foreach (var width in new[] { 1, 8, 32, 64, 129 })
        foreach (var signed in new[] { false, true })
        {
            var limit = Math.ScaleB(1, signed ? width - 1 : width);
            foreach (var number in new[] { -0.9, -1.1, 0.9, -limit, Math.BitDecrement(-limit), Math.BitIncrement(-limit),
                limit, Math.BitDecrement(limit), Math.BitIncrement(limit) })
            {
                var integer = new BigInteger(number);
                var min = signed ? -(BigInteger.One << (width - 1)) : BigInteger.Zero;
                var max = (BigInteger.One << (signed ? width - 1 : width)) - 1;
                var expected = integer < min || integer > max ? EvaluationResult.Undefined : EvaluationResult.Defined(integer & Mask(width));
                var term = table.Apply(new CoreOperator(signed ? FloatToSigned : FloatToUnsigned), width,
                    table.Constant(BitConverter.DoubleToUInt64Bits(number), 64));
                a.True(TermEvaluator.Equivalent(new TermEvaluator(_ => 0).Evaluate(term), expected, width),
                    $"浮点转整数边界 width={width} signed={signed} number={number:R}");
            }
        }
        // 两次舍入的反例：精确整数略高于 float 的中点。
        var halfway = (BigInteger.One << 80) + (BigInteger.One << 56) + 1;
        var conversion = table.Apply(new CoreOperator(UnsignedToFloat), 32, table.Constant(halfway, 81));
        a.True(new TermEvaluator(_ => 0).Evaluate(conversion).Bits == BitConverter.SingleToUInt32Bits(MathF.BitIncrement(MathF.ScaleB(1, 80))), "宽整数到 float 只舍入一次");
    }
}
