using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Analysis;

[Flags]
public enum EffectKind { None = 0, Read = 1, Write = 2, Throw = 4, Allocate = 8, ClassInitialization = 16, Synchronize = 32, Unknown = 64 }

/// <summary>保守副作用查询；没有方法摘要的调用始终视为未知读写和可抛出。</summary>
public static class ManagedEffects
{
    public static EffectKind Of(ManagedValue value)
    {
        var own = value switch
        {
            ConstantValue or LocalValue or ArgumentValue or StringValue or TypeHandleValue or ConversionValue
                or ComparisonValue or ChoiceValue or BooleanValue or NegatedValue or UnaryValue or ComposedValue
                or IsInstValue or AddressValue or PointerOffsetValue => EffectKind.None,
            BinaryValue { Op: BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem } => EffectKind.Throw,
            BinaryValue => EffectKind.None,
            FieldValue or ArrayLengthValue or ArrayElementValue or IndirectValue or PinnedArrayValue => EffectKind.Read | EffectKind.Throw,
            StaticFieldValue => EffectKind.Read | EffectKind.ClassInitialization | EffectKind.Throw,
            NewObjectValue or NewArrayValue or BoxValue or DelegateValue => EffectKind.Allocate | EffectKind.Throw,
            CheckedCastValue or UnboxAddressValue or UnboxValue => EffectKind.Throw,
            AsyncResultValue => EffectKind.Allocate | EffectKind.Throw,
            _ => EffectKind.Unknown | EffectKind.Read | EffectKind.Write | EffectKind.Throw,
        };
        return ManagedValues.Children(value).Aggregate(own, (effect, child) => effect | Of(child));
    }

    public static EffectKind Of(ManagedStatement statement)
    {
        var own = statement switch
        {
            ManagedAssignment or ManagedJump or ManagedBranch or ManagedSwitch or ManagedReturn => EffectKind.None,
            ManagedStore => EffectKind.Write,
            ManagedCheck or ManagedThrow or ManagedRethrow => EffectKind.Throw,
            ManagedEndFault => EffectKind.None,
            _ => EffectKind.Unknown | EffectKind.Read | EffectKind.Write | EffectKind.Throw,
        };
        return ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Aggregate(own, (effect, value) => effect | Of(value));
    }

    public static bool CanMoveAcrossExceptionBoundary(ManagedValue value) => Of(value) == EffectKind.None;
}
