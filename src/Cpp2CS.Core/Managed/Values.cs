using Cpp2CS.Ir;

namespace Cpp2CS.Managed;

/// <summary>带托管类型的值。Width 是值在机器上的位宽（比较结果为 1，bool 字段为 8）。</summary>
public abstract record ManagedValue(TypeRef Type, int Width);
/// <summary>方法参数；Index 为 -1 表示 this。</summary>
public sealed record ArgumentValue(int Index, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>SSA 变量对应的局部变量。</summary>
public sealed record LocalValue(Variable Variable, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>Bits 保存原始位型，浮点常量也不经过数值转换。</summary>
public sealed record ConstantValue(ulong Bits, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record StringValue(string Text, TypeRef Type) : ManagedValue(Type, 64);
public sealed record TypeHandleValue(TypeRef Target, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record NewArrayValue(ArrayRef ArrayType, ManagedValue Length) : ManagedValue(ArrayType, 64);
public sealed record NewObjectValue(MethodRef Constructor, IReadOnlyList<ManagedValue> Arguments) : ManagedValue(Constructor.DeclaringType, 64)
{
    /// <summary>原生代码内联了这个构造函数：执行对照按构造函数的方法体透明执行。</summary>
    public bool Transparent { get; init; }
}
public enum DelegateBinding { Static, ClosedInstance, VirtualInstance }
/// <summary>方法身份只来自直接 Method 符号；不表示虚表选择、开放绑定或方法身份的 φ。</summary>
public sealed record DelegateValue(DefinitionRef DelegateType, ManagedValue Target, MethodRef Method, DelegateBinding Binding) : ManagedValue(DelegateType, 64);
/// <summary>把 Operand 按 Boxed 类型装箱（Boxed 决定对象的运行时类型，与 Operand 的整数符号无关）。</summary>
public sealed record BoxValue(ManagedValue Operand, TypeRef Boxed, TypeRef ObjectType) : ManagedValue(ObjectType, 64);
/// <summary>拆箱后的托管地址；保留 unbox 的判空与类型检查。</summary>
public sealed record UnboxAddressValue(ManagedValue Operand, TypeRef Target) : ManagedValue(new ByRefRef(Target), 64);
/// <summary>按目标类型执行 unbox.any；引用、值类型和 Nullable 均保留 CLR 的检查语义。</summary>
public sealed record UnboxValue(ManagedValue Operand, TypeRef Target, int Width) : ManagedValue(Target, Width);
/// <summary>isinst：Operand 是 Target 类型（或其子类、实现）时为 Operand，否则为 null。</summary>
public sealed record IsInstValue(ManagedValue Operand, TypeRef Target, TypeRef? BoxedType = null) : ManagedValue(BoxedType ?? Target, 64);
/// <summary>引用类型显式转换；null 原样通过，非兼容对象抛 InvalidCastException。</summary>
public sealed record CheckedCastValue(ManagedValue Operand, TypeRef Target) : ManagedValue(Target, 64);
public sealed record ArrayLengthValue(ManagedValue Array, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ArrayElementValue(ManagedValue Array, ManagedValue Index, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record FieldValue(ManagedValue Receiver, FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width)
{
    /// <summary>F9 认回证明；保留原字段的求值位置，避免把条件表达式里的调用提前执行。</summary>
    public FieldAccessor? Accessor { get; init; }
}
/// <summary>根或字段存储位置的托管地址；不把机器地址当整数。</summary>
public sealed record AddressValue(ManagedValue Target) : ManagedValue(new ByRefRef(Target.Type), 64);
/// <summary>固定数组并取得首元素地址；null 或空数组返回空指针。</summary>
public sealed record PinnedArrayValue(ManagedValue Array, ArrayRef ArrayType) : ManagedValue(new PointerRef(ArrayType.Element), 64);
/// <summary>非托管指针按字节偏移，不增加数组边界检查。</summary>
public sealed record PointerOffsetValue(ManagedValue Pointer, ManagedValue Offset) : ManagedValue(Pointer.Type, 64);
/// <summary>叶子均已证明的结构体值；L4 用 initobj 和逐叶子写入构造。</summary>
public sealed record ComposedValue(TypeRef StructType, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> Leaves) : ManagedValue(StructType, 0);
/// <summary>读取/写入已定型的结构体根，地址必须由托管存储位置证明。</summary>
public sealed record IndirectValue(ManagedValue Address, TypeRef Type, int Width = 0) : ManagedValue(Type, Width);
public sealed record StaticFieldValue(FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width)
{
    public FieldAccessor? Accessor { get; init; }
}
public sealed record BinaryValue(BinOp Op, ManagedValue Left, ManagedValue Right, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record UnaryValue(UnOp Op, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ConversionValue(ConvKind Kind, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ComparisonValue(Cond Condition, ManagedValue Left, ManagedValue Right, TypeRef Type) : ManagedValue(Type, 1);
public sealed record ChoiceValue(ManagedValue Condition, ManagedValue True, ManagedValue False, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record BooleanValue(bool IsAnd, ManagedValue Left, ManagedValue Right, TypeRef Type) : ManagedValue(Type, 1);
public sealed record NegatedValue(ManagedValue Operand, TypeRef Type) : ManagedValue(Type, 1);
/// <summary>async 方法的返回（只出现在 源码视图提升 提升出的方法体里）：以 Value（无结果时为 null）完成的任务，Type 是入口方法的返回类型。</summary>
public sealed record AsyncResultValue(ManagedValue? Value, TypeRef Type) : ManagedValue(Type, 0);
/// <summary>部分方法体中未恢复的值（只出现在 <see cref="MethodRecoveryResult.Partial"/> 里）。</summary>
public sealed record HoleValue(string Reason, TypeRef Type, int Width) : ManagedValue(Type, Width);

/// <summary>托管调用。Receiver 为 null 表示静态调用；Virtual 为真时按 callvirt 分派（并对接收者判空）。不含隐藏的 MethodInfo* 参数。</summary>
public sealed record ManagedInvocation(MethodRef Method, ManagedValue? Receiver, IReadOnlyList<ManagedValue> Arguments, bool Virtual)
{
    public TypeRef? Constraint { get; init; }
}
