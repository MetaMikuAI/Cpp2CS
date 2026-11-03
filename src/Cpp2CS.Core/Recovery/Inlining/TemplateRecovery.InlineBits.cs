using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    /// <summary>证明项中的 0/1 等价：布尔值、保留低位的转换、条件选值及掩码表达同一个值。</summary>
    private ManagedValue NormalizeBit(ManagedValue value)
    {
        ManagedValue Not(ManagedValue bit) => bit switch
        {
            NegatedValue negated => negated.Operand,
            ConstantValue constant => new ConstantValue(constant.Bits == 0 ? 1UL : 0UL, types.Boolean, 8),
            _ => new NegatedValue(bit, types.Boolean),
        };
        ManagedValue? Bit(ManagedValue v) => v switch
        {
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Width: > 0 } conversion => Bit(conversion.Operand),
            ChoiceValue { True: ConstantValue { Bits: 1 }, False: ConstantValue { Bits: 0 } } choice => Bit(choice.Condition),
            ChoiceValue { True: ConstantValue { Bits: 0 }, False: ConstantValue { Bits: 1 } } choice when Bit(choice.Condition) is { } condition => Not(condition),
            BinaryValue { Op: BinOp.And, Right: ConstantValue mask } binary when (mask.Bits & 1) != 0 => Bit(binary.Left),
            ComparisonValue { Condition: Cond.Eq or Cond.Ne, Right: ConstantValue { Bits: 0 or 1 } constant } comparison when Bit(comparison.Left) is { } bit
                => (comparison.Condition == Cond.Ne) == (constant.Bits == 0) ? bit : Not(bit),
            _ => types.Kind(v.Type) == TypeKind.Bool ? v : null,
        };
        if (Bit(value) is not { } boolean) return value;
        return types.Kind(value.Type) == TypeKind.Bool ? boolean
            : types.Kind(value.Type) == TypeKind.Int ? new ConversionValue(ConvKind.ZeroExtend, boolean, value.Type, value.Width) : value;
    }
}
