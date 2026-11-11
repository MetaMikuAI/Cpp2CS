namespace Cpp2CS.Managed;

/// <summary>带托管类型的值。Width 是托管值表示的位数（比较结果为 1，bool 字段为 8）。</summary>
public abstract record ManagedValue(TypeRef Type, int Width);
/// <summary>方法参数；Index 为 -1 表示 this。</summary>
public sealed record ArgumentValue(int Index, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>方法内的局部变量；身份不包含类型与位宽。</summary>
public sealed record LocalValue(LocalId Id, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>Bits 保存原始位型，浮点常量也不经过数值转换。</summary>
public sealed record ConstantValue(ulong Bits, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record StringValue(string Text, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record TypeHandleValue(TypeRef Target, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>值类型的存储大小（IL sizeof，int32）。泛型定义里随类型实参变化。</summary>
public sealed record SizeOfValue(TypeRef Target, TypeRef Type) : ManagedValue(Type, 32);
/// <summary>ldtoken 字段：数组初始化器的 RuntimeFieldHandle。</summary>
public sealed record FieldHandleValue(FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>ldtoken 方法：表达式树中的 RuntimeMethodHandle。</summary>
public sealed record MethodHandleValue(MethodRef Method, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>表达式里的无参静态调用（async 的 sm.&lt;&gt;t__builder = Builder.Create()），Roslyn 不经过局部，反编译器按这个形态识别。Inlined 含义同 <see cref="ManagedCall.Inlined"/>。</summary>
public sealed record StaticCallValue(MethodRef Method, TypeRef Type, int Width, bool Inlined) : ManagedValue(Type, Width);
public sealed record NewArrayValue(ArrayRef ArrayType, ManagedValue Length, int Width) : ManagedValue(ArrayType, Width);
public sealed record NewObjectValue(MethodRef Constructor, IReadOnlyList<ManagedValue> Arguments, int Width) : ManagedValue(Constructor.DeclaringType, Width)
{
    /// <summary>原生代码内联了这个构造函数：执行对照按构造函数的方法体透明执行。</summary>
    public bool Transparent { get; init; }
}
public enum DelegateBinding { Static, ClosedInstance, VirtualInstance }
/// <summary>方法身份只来自直接 Method 符号；不表示虚表选择、开放绑定或方法身份的 φ。</summary>
public sealed record DelegateValue(DefinitionRef DelegateType, ManagedValue Target, MethodRef Method, DelegateBinding Binding, int Width) : ManagedValue(DelegateType, Width);
/// <summary>把 Operand 按 Boxed 类型装箱（Boxed 决定对象的运行时类型，与 Operand 的整数符号无关）。</summary>
public sealed record BoxValue(ManagedValue Operand, TypeRef Boxed, TypeRef ObjectType, int Width) : ManagedValue(ObjectType, Width);
/// <summary>拆箱后的托管地址；保留 unbox 的判空与类型检查。</summary>
public sealed record UnboxAddressValue(ManagedValue Operand, TypeRef Target, int Width) : ManagedValue(new ByRefRef(Target), Width);
/// <summary>按目标类型执行 unbox.any；引用、值类型和 Nullable 均保留 CLR 的检查语义。</summary>
public sealed record UnboxValue(ManagedValue Operand, TypeRef Target, int Width) : ManagedValue(Target, Width);
/// <summary>isinst：Operand 是 Target 类型（或其子类、实现）时为 Operand，否则为 null。</summary>
public sealed record IsInstValue(ManagedValue Operand, TypeRef Target, int Width, TypeRef? BoxedType = null) : ManagedValue(BoxedType ?? Target, Width);
/// <summary>引用类型显式转换；null 原样通过，非兼容对象抛 InvalidCastException。</summary>
public sealed record CheckedCastValue(ManagedValue Operand, TypeRef Target, int Width) : ManagedValue(Target, Width);
public sealed record ArrayLengthValue(ManagedValue Array, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record StringLengthValue(ManagedValue String, TypeRef Type) : ManagedValue(Type, 32);
public sealed record ArrayElementValue(ManagedValue Array, ManagedValue Index, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>多维数组的元素：读写与取址写出为数组类型的 Get、Set、Address（ECMA-335 II.14.2），各维下标为 int32，越界抛出 IndexOutOfRangeException。</summary>
public sealed record MultiArrayElementValue(ManagedValue Array, IReadOnlyList<ManagedValue> Indices, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>分配多维数组：newobj 数组类型的构造函数，各维长度为 int32。</summary>
public sealed record NewMultiArrayValue(ArrayRef ArrayType, IReadOnlyList<ManagedValue> Lengths, int Width) : ManagedValue(ArrayType, Width);
/// <summary>数组一维的长度或下界（System.Array.GetLength / GetLowerBound，int32）。</summary>
public sealed record ArrayBoundValue(ManagedValue Array, int Dimension, bool Lower, TypeRef Type) : ManagedValue(Type, 32);
public sealed record FieldValue(ManagedValue Receiver, FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width)
{
    /// <summary>F9 认回证明；保留原字段的求值位置，避免把条件表达式里的调用提前执行。</summary>
    public FieldAccessor? Accessor { get; init; }
    public PendingAccess? Pending { get; init; }
    /// <summary>内联的逆没有证明、按原生代码直接访问的同程序集字段；写出时不按访问权限拒绝，源码由主程序集声明的放宽承接。</summary>
    public bool Unfolded { get; init; }
}
/// <summary>对调用方不可访问、等待内联的逆证明的访问：原生地址、证明失败时洞的原因与是否为写入。只在恢复过程中出现。</summary>
public sealed record PendingAccess(ulong Address, string Reason, bool Write);
/// <summary>根或字段存储位置的托管地址。</summary>
public sealed record AddressValue(ManagedValue Target, int Width) : ManagedValue(new ByRefRef(Target.Type), Width);
/// <summary>固定数组并取得首元素地址；null 或空数组返回空指针。</summary>
public sealed record PinnedArrayValue(ManagedValue Array, ArrayRef ArrayType, int Width) : ManagedValue(new PointerRef(ArrayType.Element), Width);
/// <summary>非托管指针按字节偏移，不增加数组边界检查。</summary>
public sealed record PointerOffsetValue(ManagedValue Pointer, ManagedValue Offset, int Width) : ManagedValue(Pointer.Type, Width);
/// <summary>叶子均已证明的结构体值；L4 用 initobj 和逐叶子写入构造。</summary>
public sealed record ComposedValue(TypeRef StructType, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> Leaves) : ManagedValue(StructType, 0)
{
    /// <summary>有同程序集的不可访问叶子、构造没有证明，按原生代码逐个写入；见 <see cref="FieldValue.Unfolded"/>。</summary>
    public bool Unfolded { get; init; }
}
/// <summary>读取/写入已定型的结构体根，地址必须由托管存储位置证明。</summary>
public sealed record IndirectValue(ManagedValue Address, TypeRef Type, int Width = 0) : ManagedValue(Type, Width);
public sealed record StaticFieldValue(FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width)
{
    public FieldAccessor? Accessor { get; init; }
    public PendingAccess? Pending { get; init; }
    /// <summary>见 <see cref="FieldValue.Unfolded"/>。</summary>
    public bool Unfolded { get; init; }
}
public sealed record BinaryValue(BinaryOperator Op, ManagedValue Left, ManagedValue Right, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record UnaryValue(UnaryOperator Op, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ConversionValue(ConversionKind Kind, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ComparisonValue(ComparisonKind Condition, ManagedValue Left, ManagedValue Right, TypeRef Type) : ManagedValue(Type, 1);
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
