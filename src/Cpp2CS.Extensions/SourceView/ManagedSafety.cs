using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>由路径非空事实和已证明访问器支持的读取安全性；未知调用不作推断。</summary>
internal static class ManagedSafety
{
    public static bool Receiver(ManagedValue value, IReadOnlySet<ManagedValue> nonnull, Func<MethodRef, bool>? getter) => value switch
    {
        // C# 实例方法中的 this；普通参数仍需路径上的非空证据。
        ArgumentValue { Index: -1, Type: DefinitionRef { Definition.IsValueType: false } } => true,
        LocalValue or ArgumentValue => nonnull.Contains(value) || value.Type is DefinitionRef { Definition.IsValueType: true },
        AddressValue address => address.Target.Type is DefinitionRef { Definition.IsValueType: true }
            && address.Target is LocalValue or ArgumentValue or FieldValue && NonThrowingRead(address.Target, nonnull, getter),
        _ => false,
    };

    public static bool NonThrowingRead(ManagedValue value, IReadOnlySet<ManagedValue> nonnull, Func<MethodRef, bool>? getter) => value switch
    {
        LocalValue or ArgumentValue or ConstantValue => true,
        FieldValue field => Receiver(field.Receiver, nonnull, getter)
            && !field.Field.Field.IsStatic && (field.Accessor is null || !field.Accessor.Write && getter?.Invoke(field.Accessor.Method) == true),
        ConversionValue conversion => ManagedTypes.PrimitiveName(conversion.Type) is not null
            && ManagedTypes.PrimitiveName(conversion.Operand.Type) is not null && NonThrowingRead(conversion.Operand, nonnull, getter),
        BinaryValue
        {
            Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor
            or BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv
        } binary
            => NonThrowingRead(binary.Left, nonnull, getter) && NonThrowingRead(binary.Right, nonnull, getter),
        ComparisonValue comparison => NonThrowingRead(comparison.Left, nonnull, getter) && NonThrowingRead(comparison.Right, nonnull, getter),
        ChoiceValue choice => NonThrowingRead(choice.Condition, nonnull, getter) && NonThrowingRead(choice.True, nonnull, getter) && NonThrowingRead(choice.False, nonnull, getter),
        BooleanValue boolean => NonThrowingRead(boolean.Left, nonnull, getter) && NonThrowingRead(boolean.Right, nonnull, getter),
        NegatedValue negated => NonThrowingRead(negated.Operand, nonnull, getter),
        _ => false,
    };

}
