using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Kernel.Forward;

/// <summary>
/// 一个类型在展开时需要知道的形状：栈上的类别、存储位宽、小整数的符号、实体身份。
/// 指针大小的类型（对象引用、地址、本机整数）的存储位宽就是指针位宽。
/// </summary>
public sealed record TypeShape(StackKind Kind, int StorageBits, bool Signed, EntityRef Entity)
{
    /// <summary>在求值栈上的位宽。</summary>
    public int StackBits => Kind == StackKind.Int32 ? 32 : StorageBits;
}

/// <summary>方法的形状。Parameters 含 this（实例方法的第 0 个）；Return 为空表示 void。</summary>
public sealed record MethodShape(EntityRef Entity, bool HasThis, ImmutableArray<TypeShape> Parameters, TypeShape? Return, VariantCondition Dispatch);

/// <summary>
/// 字段的形状。HasInitializer：所属的类有静态构造函数；PreciseInitialization：初始化的时机是精确的（没有 beforefieldinit）。
/// OffsetBits：值类型的实例字段在值里的位偏移，未知时为 -1。
/// </summary>
public sealed record FieldShape(EntityRef Entity, EntityRef DeclaringType, TypeShape Type, bool IsStatic, bool HasInitializer,
    bool PreciseInitialization, int OffsetBits);

/// <summary>方法体：签名、局部变量、IL 字节、异常处理区域的个数。</summary>
public sealed record MethodBody(MethodShape Method, ImmutableArray<TypeShape> Locals, ImmutableArray<byte> Code, int ExceptionRegions);

/// <summary>
/// 展开时对元数据的全部需求。记号是方法体里的元数据记号；解析不了时抛出 <see cref="ExpansionException"/>。
/// 实体身份由实现分配，内核只比较与传递。
/// </summary>
public interface IMetadataView
{
    MethodShape Method(int token);
    FieldShape Field(int token);
    TypeShape Type(int token);
}

/// <summary>方法体不能按目录展开。Reason 是原因的类别，Offset 是指令的偏移（与指令无关时为 -1）。</summary>
public sealed class ExpansionException : Exception
{
    public string Reason { get; }
    public int Offset { get; }

    public ExpansionException(string reason, string detail, int offset = -1) : base(detail.Length == 0 ? reason : $"{reason}：{detail}")
    {
        Reason = reason;
        Offset = offset;
    }
}
