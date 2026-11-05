using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Effects;

/// <summary>托管 IR 的效果。附加证明只处理调用方自己的证据值，不根据名称假定调用为纯。</summary>
public static class ManagedEffects
{
    public static EffectSummary Value(ManagedValue value, Func<ManagedValue, EffectSummary?>? evidence = null)
    {
        if (evidence?.Invoke(value) is { } proven) return proven;
        EffectSummary Read(MemoryKind kind) => EffectSummary.Access(kind);
        var own = value switch
        {
            LocalValue or ArgumentValue or ConstantValue or StringValue or TypeHandleValue or FieldHandleValue or MethodHandleValue => EffectSummary.None,
            FieldValue { Accessor: not null } or StaticFieldValue { Accessor: not null } => EffectSummary.Unknown,
            FieldValue f => Read(f.Receiver.Type is DefinitionRef { Definition.IsValueType: true }
                or ByRefRef { Element: DefinitionRef { Definition.IsValueType: true } } ? MemoryKind.Local : MemoryKind.Instance),
            StaticFieldValue => Read(MemoryKind.Static),
            ArrayLengthValue or StringLengthValue => Read(MemoryKind.Instance),
            ArrayElementValue => Read(MemoryKind.Element),
            IndirectValue { Address: AddressValue { Target: LocalValue } } => Read(MemoryKind.Local),
            IndirectValue => Read(MemoryKind.Reference),
            AddressValue address => Address(address.Target, evidence),
            NewObjectValue => EffectSummary.Unknown,
            NewArrayValue or BoxValue or DelegateValue => new(EffectKind.Allocate, ExceptionEffect.Any),
            CheckedCastValue or UnboxAddressValue or UnboxValue => new(EffectKind.None, ExceptionEffect.Any),
            BinaryValue { Op: BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem } => new(EffectKind.None, ExceptionEffect.Other),
            BinaryValue or UnaryValue or ConversionValue or ComparisonValue or BooleanValue or NegatedValue
                or ChoiceValue or ComposedValue or IsInstValue or PointerOffsetValue => EffectSummary.None,
            _ => EffectSummary.Unknown,
        };
        // 取址只计算位置，不读取目标；其子项已经由 Address 分析。
        if (value is AddressValue) return own;
        foreach (var child in ManagedValues.Children(value)) own |= Value(child, evidence);
        return own;
    }

    private static EffectSummary Address(ManagedValue target, Func<ManagedValue, EffectSummary?>? evidence)
    {
        EffectSummary Access(MemoryKind kind) => EffectSummary.Access(kind) with { Kinds =
            kind == MemoryKind.Static ? EffectKind.Initialize : EffectKind.None };
        return target switch
        {
            LocalValue or ArgumentValue => EffectSummary.None,
            FieldValue { Accessor: not null } or StaticFieldValue { Accessor: not null } => EffectSummary.Unknown,
            FieldValue f => Value(f.Receiver, evidence) | Access(f.Receiver.Type is DefinitionRef { Definition.IsValueType: true }
                or ByRefRef { Element: DefinitionRef { Definition.IsValueType: true } } ? MemoryKind.Local : MemoryKind.Instance),
            StaticFieldValue => Access(MemoryKind.Static),
            ArrayElementValue a => Value(a.Array, evidence) | Value(a.Index, evidence) | Access(MemoryKind.Element),
            IndirectValue i => Value(i.Address, evidence),
            _ => EffectSummary.Unknown,
        };
    }

    public static EffectSummary Invocation(ManagedInvocation invocation) => EffectSummary.Unknown;

    public static EffectSummary Statement(ManagedStatement statement, Func<ManagedValue, EffectSummary?>? evidence = null)
    {
        var effect = statement switch
        {
            ManagedCall c => Invocation(c.Invocation),
            ManagedStore => new EffectSummary(EffectKind.Write),
            ManagedThrow or ManagedRethrow or ManagedCheck => new(EffectKind.None, ExceptionEffect.Any),
            ManagedAssignment or ManagedReturn or ManagedJump or ManagedBranch or ManagedSwitch or ManagedEndFault => EffectSummary.None,
            _ => EffectSummary.Unknown,
        };
        foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement))) effect |= Value(value, evidence);
        return effect;
    }
}
