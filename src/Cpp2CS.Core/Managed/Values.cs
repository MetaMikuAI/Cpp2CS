using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>带托管类型的值；Width 保留原始位宽，整数运算尚未按 C# 的提升规则改写。</summary>
public abstract record ManagedValue(TypeRef Type, int Width);
public sealed record ArgumentValue(int Index, string Name, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record LocalValue(Variable Variable, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>按栈区域共享的可变局部存储，不是寄存器 SSA 值。</summary>
public sealed record StackLocalValue(long Offset, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record AddressValue(ManagedValue Target, ByRefRef ReferenceType) : ManagedValue(ReferenceType, 64);
public sealed record AggregateMember(IReadOnlyList<FieldRef> Path, ManagedValue Value);
/// <summary>按字段组装值类型；不调用构造函数，不复制未知填充字节。</summary>
public sealed record AggregateValue(TypeRef Type, int Width, IReadOnlyList<AggregateMember> Members) : ManagedValue(Type, Width);
public sealed record DefaultValue(TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>Bits 保存原始位型，浮点常量也不经过整数到浮点的数值转换。</summary>
public sealed record ConstantValue(ulong Bits, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record StringValue(string Text, TypeRef Type) : ManagedValue(Type, 64);
public sealed record TypeHandleValue(TypeRef TargetType, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record NewArrayValue(ArrayRef ArrayType, ManagedValue Length) : ManagedValue(ArrayType, 64);
/// <summary>清零分配并初始化类型，不执行实例构造函数；后续调用和字段访问保持原位置。</summary>
public sealed record ObjectAllocationValue(DefinitionRef ObjectType) : ManagedValue(ObjectType, 64);
public sealed record NewObjectValue(MethodRef Constructor, IReadOnlyList<ManagedValue> Arguments) : ManagedValue(Constructor.DeclaringType, 64);
/// <summary>在当前位置复制值并装箱；nullable 沿用 CLR 的空值和内部值装箱规则。</summary>
public sealed record BoxInitialization(TypeRef TargetType, MethodRef RunClassConstructor, MethodRef? HasValue, MethodRef? GetValueOrDefault);
public sealed record BoxValue(ManagedValue Operand, TypeRef ObjectType, BoxInitialization? Initialization = null) : ManagedValue(ObjectType, 64);
public sealed record ArrayLengthValue(ManagedValue Array, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ArrayElementValue(ManagedValue Array, ManagedValue Index, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record FieldValue(ManagedValue Receiver, FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record StaticFieldValue(FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record IndirectValue(ManagedValue Address, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record InvocationValue(ManagedInvocation Invocation, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record BinaryValue(BinOp Op, ManagedValue Left, ManagedValue Right, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record UnaryValue(UnOp Op, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ConversionValue(ConvKind Kind, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ComparisonValue(Cond Condition, ManagedValue Left, ManagedValue Right, TypeRef Type) : ManagedValue(Type, 1);
public sealed record ChoiceValue(ManagedValue Condition, ManagedValue True, ManagedValue False, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record BooleanValue(bool IsAnd, ManagedValue Left, ManagedValue Right, TypeRef Type) : ManagedValue(Type, 1);
public sealed record NegatedValue(ManagedValue Operand, TypeRef Type) : ManagedValue(Type, 1);

/// <summary>直接托管调用的逻辑参数，排除隐藏 MethodInfo；Receiver 为 null 表示静态调用。</summary>
public sealed record ManagedInvocation(MethodRef Method, ManagedValue? Receiver, IReadOnlyList<ManagedValue> Arguments);
