using System.Numerics;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private bool IsFloat(TypeRef type) => types.Kind(type) is TypeKind.Float or TypeKind.Double;
    private TypeRef FloatType(int width) => width == 32 ? types.Single : types.Double;
    private ManagedValue IntegerBits(ManagedValue value) => IsFloat(value.Type)
        ? new ConversionValue(ConversionKind.Bitcast, value, StackType(value.Width), value.Width)
        : ManagedTypes.IsNativePointer(value.Type) ? NativeIntegerBits(value) : value;
    private ManagedValue FloatBits(ManagedValue value, int width)
    {
        if (IsFloat(value.Type)) return value;
        if (ManagedTypes.IsNativePointer(value.Type)) value = IntegerBits(value);
        // 常量保存原始位型；不经整数到浮点的数值转换。
        if (value is ConstantValue c) return new ConstantValue(c.Bits, FloatType(width), width);
        if (value is ConversionValue { Kind: ConversionKind.Bitcast } cast && IsFloat(cast.Operand.Type)) return cast.Operand;
        return new ConversionValue(ConversionKind.Bitcast, value, FloatType(width), width);
    }

    private static bool IsOperation(Term term, CoreOperation op) => term.Operator is CoreOperator c && c.Operation == op;

    // conv.i/u 的定义域内必须相等；NaN 和截断结果越界时 IL 未规定结果。
    // 每个选择的替代臂必须是常量，且条件只能选中定义域外，或选中恰好等于下界的值。
    // 这是各臂的定义域判据，不依赖指令、寄存器或选择的排列次序。
    private static Term? ConversionRefinement(Term term)
    {
        if (term.Operator is CoreOperator { Operation: CoreOperation.FloatToSigned or CoreOperation.FloatToUnsigned })
            return term.Width is 32 or 64 && term.Operands[0].Width is 32 or 64 ? term : null;
        if (!IsOperation(term, CoreOperation.Select) || term.Operands[1].Kind != TermKind.Constant) return null;
        var conversion = ConversionRefinement(term.Operands[2]);
        if (conversion is null) return null;
        var input = conversion.Operands[0];
        var condition = term.Operands[0];
        var source = IsOperation(input, CoreOperation.FloatTruncate) ? input.Operands[0] : input;
        if (IsOperation(condition, CoreOperation.FloatUnordered)
            && (condition.Operands[0] == source || condition.Operands[0] == input)
            && (condition.Operands[1] == source || condition.Operands[1] == input)) return conversion;
        bool unsigned = IsOperation(conversion, CoreOperation.FloatToUnsigned);
        int exponent = unsigned ? conversion.Width : conversion.Width - 1;
        double limit = Math.ScaleB(1, exponent);
        // 与定义域外常量相等的臂同样不约束 IL；例如运行时转换模板对正无穷的替代值。
        if (IsOperation(condition, CoreOperation.FloatEqual))
        {
            Term? constant = condition.Operands[0] == source ? condition.Operands[1]
                : condition.Operands[1] == source ? condition.Operands[0] : null;
            if (constant?.ConstantValue is { } bits && constant.Width == source.Width)
            {
                double number = constant.Width == 32 ? BitConverter.UInt32BitsToSingle((uint)bits) : BitConverter.UInt64BitsToDouble((ulong)bits);
                double truncated = Math.Truncate(number);
                if (!double.IsFinite(number) || truncated < (unsigned ? 0 : -limit) || truncated >= limit) return conversion;
            }
        }
        if (!IsOperation(condition, CoreOperation.FloatLessEqual) || !IsOperation(input, CoreOperation.FloatTruncate)) return null;
        bool Bound(Term value, double expected) => value.Kind == TermKind.Constant && value.Width == input.Width
            && value.ConstantValue == (input.Width == 32 ? new BigInteger(BitConverter.SingleToUInt32Bits((float)expected))
                : new BigInteger(BitConverter.DoubleToUInt64Bits(expected)));
        // 上界是开区间，>= 2^n 的替代值完全处于 IL 未定义域。
        if (condition.Operands[1] == input && Bound(condition.Operands[0], limit)) return conversion;
        // 下界包含在定义域内，等号处的替代值必须与转换相等。
        BigInteger minimum = unsigned ? BigInteger.Zero : BigInteger.One << (conversion.Width - 1);
        if (condition.Operands[0] == input && Bound(condition.Operands[1], unsigned ? 0 : -limit)
            && term.Operands[1].ConstantValue == minimum) return conversion;
        return null;
    }

    private ManagedValue? FloatOperation(Term term, CoreOperation op)
    {
        int width = term.Width, inputWidth = term.Operands[0].Width;
        bool integerInput = op is CoreOperation.SignedToFloat or CoreOperation.UnsignedToFloat;
        bool integerOutput = op is CoreOperation.FloatToSigned or CoreOperation.FloatToUnsigned;
        if ((!integerInput && inputWidth is not (32 or 64)) || (width != 1 && width is not (32 or 64)))
            return Fail<ManagedValue>(LoweringFailureKind.FloatingOrVector, $"不支持的浮点格式或转换位宽：{op}/{inputWidth}/{width}");
        if (op is CoreOperation.FloatRemainder or CoreOperation.FloatFusedMultiplyAdd
            or CoreOperation.FloatMinimum or CoreOperation.FloatMaximum or CoreOperation.FloatMinimumNumber or CoreOperation.FloatMaximumNumber)
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedOperation, $"Managed 缺少对应浮点运算：{op}");
        // 向零取整不改变随后向零整数转换的值或定义域。
        var operands = term.Operands.Select(t => Value(integerOutput && IsOperation(t, CoreOperation.FloatTruncate) ? t.Operands[0] : t, !integerInput)).ToArray();
        if (operands.Any(v => v is null)) return null;
        var a = integerInput ? IntegerBits(operands[0]!) : FloatBits(operands[0]!, inputWidth);
        var b = operands.Length > 1 ? FloatBits(operands[1]!, inputWidth) : null;
        var type = FloatType(width);
        if (integerInput)
            return new ConversionValue(op == CoreOperation.SignedToFloat ? ConversionKind.SignedIntegerToFloat : ConversionKind.UnsignedIntegerToFloat,
                op == CoreOperation.SignedToFloat ? Signed(a, inputWidth) : Mask(a, inputWidth), type, width);
        if (integerOutput)
            return new ConversionValue(op == CoreOperation.FloatToSigned ? ConversionKind.FloatToSignedInteger : ConversionKind.FloatToUnsignedInteger,
                a, StackType(width), width);
        if (op == CoreOperation.FloatConvert) return new ConversionValue(ConversionKind.FloatToFloat, a, type, width);
        ComparisonKind? comparison = op switch
        {
            CoreOperation.FloatEqual => ComparisonKind.FloatEqual,
            // 核心 NotEqual 包含无序；Managed.FloatNotEqual 只表示有序不等。
            CoreOperation.FloatNotEqual => ComparisonKind.FloatUnorderedOrNotEqual,
            CoreOperation.FloatLess => ComparisonKind.FloatLess,
            CoreOperation.FloatLessEqual => ComparisonKind.FloatLessOrEqual,
            CoreOperation.FloatOrdered => ComparisonKind.FloatOrdered,
            CoreOperation.FloatUnordered => ComparisonKind.FloatUnordered,
            _ => null,
        };
        if (comparison is { } cmp) return new ComparisonValue(cmp, a, b!, types.Boolean);
        BinaryOperator? binary = op switch
        {
            CoreOperation.FloatAdd => BinaryOperator.FloatAdd, CoreOperation.FloatSubtract => BinaryOperator.FloatSubtract,
            CoreOperation.FloatMultiply => BinaryOperator.FloatMultiply, CoreOperation.FloatDivide => BinaryOperator.FloatDivide, _ => null,
        };
        if (binary is { } bin) return new BinaryValue(bin, a, b!, type, width);
        UnaryOperator? unary = op switch
        {
            CoreOperation.FloatNegate => UnaryOperator.FloatNegate, CoreOperation.FloatAbs => UnaryOperator.Abs,
            CoreOperation.FloatSqrt => UnaryOperator.Sqrt, CoreOperation.FloatFloor => UnaryOperator.Floor,
            CoreOperation.FloatCeiling => UnaryOperator.Ceiling, CoreOperation.FloatTruncate => UnaryOperator.Truncate,
            CoreOperation.FloatRoundToEven => UnaryOperator.RoundToEven, _ => null,
        };
        return unary is { } un ? new UnaryValue(un, a, type, width)
            : Fail<ManagedValue>(LoweringFailureKind.UnsupportedOperation, $"尚无等价的托管写法：{op}");
    }
}
