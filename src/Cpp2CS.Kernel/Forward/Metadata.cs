using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Kernel.Forward;

/// <summary>
/// 一个类型在展开时需要知道的形状：栈上的类别、存储位宽、小整数的符号、实体身份。
/// 指针大小的类型（对象引用、地址、本机整数）的存储位宽就是指针位宽。
/// </summary>
public sealed record TypeShape(StackKind Kind, int StorageBits, bool Signed, EntityRef Entity)
{
    internal static TypeShape? Implied(CatalogEntry entry, int pointerBits) => entry.Storage is { } storage
        ? new(storage.Kind, storage.Bits == 0 ? pointerBits : storage.Bits, storage.Signed, default) : null;

    /// <summary>在求值栈上的位宽。</summary>
    public int StackBits => Kind == StackKind.Int32 ? 32 : StorageBits;
    /// <summary>存储只取 0 与 1：生成代码把 System.Boolean 写成 C++ 的 bool，调用约定规定它的取值只有这两个（设计 16.2）。</summary>
    public bool TwoValued { get; init; }
    /// <summary>
    /// 值类型按字段递归展开之后的各基本成员，按在值里的位偏移排列；其余类型为空。
    /// 调用约定按它区分同质浮点聚合体与其他聚合体（AAPCS64 §6.8.2）。值类型的成员未知时也为空，这时传递方式不能判定。
    /// </summary>
    public ImmutableArray<AggregateMember> Members { get; init; } = [];
}

/// <summary>方法的形状。Parameters 含 this（实例方法的第 0 个）；Return 为空表示 void。</summary>
public sealed record MethodShape(EntityRef Entity, bool HasThis, ImmutableArray<TypeShape> Parameters, TypeShape? Return, VariantCondition Dispatch)
{
    /// <summary>方法是所属类的类型初始化器。</summary>
    public bool IsTypeInitializer { get; init; }
    /// <summary>所属的类。</summary>
    public EntityRef DeclaringType { get; init; }
    /// <summary>所属的类有静态构造函数。</summary>
    public bool HasInitializer { get; init; }
    /// <summary>所属的类的初始化时机是精确的（没有 beforefieldinit）。</summary>
    public bool PreciseInitialization { get; init; }
}

/// <summary>
/// 字段的形状。HasInitializer：所属的类有静态构造函数；PreciseInitialization：初始化的时机是精确的（没有 beforefieldinit）。
/// OffsetBits：值类型的实例字段在值里的位偏移，未知时为 -1。
/// </summary>
public sealed record FieldShape(EntityRef Entity, EntityRef DeclaringType, TypeShape Type, bool IsStatic, bool HasInitializer,
    bool PreciseInitialization, int OffsetBits)
{
    /// <summary>相对对象指针或普通静态区的字节偏移。</summary>
    public int? Offset { get; init; }
}

/// <summary>
/// 方法体：签名、局部变量、IL 字节、异常处理区域的个数，以及方法头是否设置了 InitLocals（局部变量在进入时清零，ECMA-335 II.25.4.4）。
/// </summary>
public sealed record MethodBody(MethodShape Method, ImmutableArray<TypeShape> Locals, ImmutableArray<byte> Code, int ExceptionRegions, bool InitLocals)
{
    /// <summary>这个方法是某个类的类型初始化器（.cctor）时，是那个类；入口处“该类的初始化已触发”成立（设计 7.7）。</summary>
    public EntityRef? InitializerOf { get; init; }
}

/// <summary>
/// 按模型实体读取形状。缺少依据时抛出 <see cref="ExpansionException"/>。
/// 实体身份由实现分配，内核只比较与传递。
/// </summary>
public interface IMetadataView
{
    MethodShape Method(EntityRef entity);
    FieldShape Field(EntityRef entity);
    TypeShape Type(EntityRef entity);
}

/// <summary>把一个模块内的记号解析为模型实体。</summary>
public interface ITokenResolver
{
    EntityRef Method(int token);
    EntityRef Field(int token);
    EntityRef Type(int token);
    /// <summary>ldstr 的字面量记号：字符串实体（设计第 8 节：字面量表里内容相同的最小下标）。</summary>
    EntityRef String(int token);
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
