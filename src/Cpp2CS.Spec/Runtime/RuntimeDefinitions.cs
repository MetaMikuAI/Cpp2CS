using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Spec.Runtime;

/// <summary>定义由实参、结果项和有定义条件组成。条件约束这次转换，即使结果被丢弃也成立。</summary>
public sealed record RuntimeTargetDefinition(RuntimeFunction Function, ImmutableArray<string> Targets, Term Argument,
    Term Value, Term DefinedWhen, string Source);

public static class RuntimeTargetDefinitions
{
    public static ImmutableArray<RuntimeTargetDefinition> Entries { get; } = DoubleToInt32();

    private static ImmutableArray<RuntimeTargetDefinition> DoubleToInt32()
    {
        const string source = "codegen/il2cpp-codegen-common.h: il2cpp_codegen_cast_double_to_int<int32_t>；C++ [conv.fpint]";
        var p = new TermPool();
        var x = p.EntryParameter(0, new(SlotKind.Managed, 0), 64);
        Term Double(double v) => p.Constant(BitConverter.DoubleToInt64Bits(v), 64);

        // 向零截断后的整数须可表示。两端均为开区间，有序比较同时排除了 NaN。
        var lower = p.Operation(Op.FLt, 1, Double((double)int.MinValue - 1), x);
        var upper = p.Operation(Op.FLt, 1, x, Double((double)int.MaxValue + 1));
        var inRange = p.And(lower, upper);
        var positiveInfinity = p.Operation(Op.FEq, 1, x, Double(double.PositiveInfinity));
        var armValue = p.Select(positiveInfinity, p.Constant(int.MinValue, 32), p.Operation(Op.FToSSaturate, 32, x));
        return [
            new(RuntimeFunction.CastDoubleToInt32, ["arm64", "armv7"], x, armValue, p.Or(positiveInfinity, inRange), source),
            new(RuntimeFunction.CastDoubleToInt32, ["x86", "x86_64"], x, p.Operation(Op.FToSIndefinite, 32, x), inRange, source),
        ];
    }
}

/// <summary>由元数据判定。普通类限于有继承层级的类，排除接口、数组、Nullable 和可按变体匹配的委托。
/// 这些类型在 vm/Class.cpp 的 Class::IsAssignableFrom 各有单独分支。层级读数以前提 HasParentUnsafe 所要求的两类均已初始化为准。</summary>
public enum RuntimeTypeCondition : byte { OrdinaryClass, SealedOrdinaryClass }

/// <summary>条件作用于指定实参；展开项与函数调用在该条件下同值。</summary>
public sealed record RuntimeEquation(RuntimeFunction Function, RuntimeTypeCondition Condition, int TypeOperand,
    ImmutableArray<Term> Arguments, Term Expansion, string Source);

public static partial class RuntimeEquations
{
    internal const string SealedSource = "codegen/il2cpp-codegen-il2cpp.h: IsInstSealed；vm/Class.cpp: Class::IsAssignableFrom";
    internal const string ClassSource = "codegen/il2cpp-codegen-il2cpp.h: IsInstClass；vm/ClassInlines.h: ClassInlines::HasParentUnsafe；vm/Class.cpp: Class::IsAssignableFrom";

    public static ImmutableArray<RuntimeEquation> IsInstance(RuntimeLayout layout)
    {
        var p = new TermPool();
        var x = p.EntryParameter(0, new(SlotKind.Managed, 0), layout.PointerBits);
        var target = p.EntryParameter(0, new(SlotKind.Managed, 1), layout.PointerBits);
        var data = new RuntimeDataTerms(p, layout);
        var nil = p.Zero(layout.PointerBits);
        var klass = data.ClassOf(x);
        var targetDepth = data.Depth(target);
        var hasParent = p.Select(p.Uge(data.Depth(klass), targetDepth), p.Eq(data.Ancestor(klass, targetDepth), target), p.False);
        Term IfInstance(Term match) => p.Select(p.Eq(x, nil), nil, p.Select(match, x, nil));
        return [
            new(RuntimeFunction.IsInstance, RuntimeTypeCondition.SealedOrdinaryClass, 1, [x, target], IfInstance(p.Eq(klass, target)), SealedSource),
            new(RuntimeFunction.IsInstance, RuntimeTypeCondition.OrdinaryClass, 1, [x, target], IfInstance(hasParent), ClassSource),
        ];
    }
}

/// <summary>按地址读取运行时不可变字段。负号区分此属性与 RuntimeFunction 编号；读取位宽是项身份的一部分。</summary>
public static class RuntimeAttributes
{
    public static AttributeId ImmutableRead { get; } = new(-1);
}

/// <summary>字段地址与读取位宽取自布局；使用这些项的分支排除空指针与越界下标。</summary>
internal sealed class RuntimeDataTerms(TermPool p, RuntimeLayout layout)
{
    public Term ClassOf(Term obj) => p.Attribute(new((int)RuntimeFunction.ClassOf), layout.PointerBits, obj);
    public Term Field(Term address, int offset, int bits) =>
        p.Attribute(RuntimeAttributes.ImmutableRead, bits, p.Add(address, p.Constant(offset, layout.PointerBits)));

    public Term Depth(Term klass) => Field(klass, layout.ClassTypeHierarchyDepthOffset, layout.ClassTypeHierarchyDepthBits);

    public Term Ancestor(Term klass, Term targetDepth)
    {
        var table = Field(klass, layout.ClassTypeHierarchyOffset, layout.PointerBits);
        var index = p.Sub(p.ZeroExtend(targetDepth, layout.PointerBits), p.Constant(1, layout.PointerBits));
        return Field(Indexed(table, index, layout.PointerBits / 8), 0, layout.PointerBits);
    }

    public Term InterfacePair(Term klass, Term index) =>
        Indexed(Field(klass, layout.ClassInterfaceOffsetsOffset, layout.PointerBits), p.ZeroExtend(index, layout.PointerBits), layout.InterfaceOffsetPairBytes);

    public Term VTableEntry(Term klass, Term pair, Term slot)
    {
        var offset = Field(pair, layout.InterfaceSlotOffset, layout.InterfaceSlotBits);
        var index = p.Add(offset, p.ZeroExtend(slot, offset.Width));
        var table = p.Add(klass, p.Constant(layout.ClassVTableOffset, layout.PointerBits));
        return Indexed(table, p.SignExtend(index, layout.PointerBits), layout.VirtualInvokeDataBytes);
    }

    private Term Indexed(Term address, Term index, int stride) =>
        p.Add(address, p.Mul(index, p.Constant(stride, layout.PointerBits)));
}
