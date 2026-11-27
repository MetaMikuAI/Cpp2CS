using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Kernel.Forward;

/// <summary>模板一侧的效果的种类。</summary>
public enum EffectKind : byte
{
    Read, Write, Call, RuntimeCall, ClassInitialize, ThrowIf,
    /// <summary>有定义条件（设计 9.1）：不是效果，操作数是条件。</summary>
    Require,
    /// <summary>新对象（设计 7.5）：分配 Entity 给出的类的对象，结果是新引用；含该类的类初始化分量，Precise 是它的时机是否精确。</summary>
    NewObject,
    /// <summary>抛出操作数给出的异常对象，不返回。</summary>
    Throw,
    /// <summary>为本次方法调用的形参或局部建立帧对象，操作数是初始内容，结果是托管指针。</summary>
    FrameObject,
}

/// <summary>
/// 模板一侧的一个效果：目录项的效果模板里的一步，形参已经换成实参。
/// 操作数的次序：读——位置的基；写——位置的基，然后是被写的值；调用——间接调用的目标（如果有），然后是各实参；
/// 条件抛出——条件；抛出——异常对象；新对象没有操作数。Entry 与 Offset 是追溯信息，不作身份，不进入摘要。
/// </summary>
public sealed class TemplateEffect : IFlowOccurrence
{
    public EffectKind Kind { get; }
    public ImmutableArray<Term> Operands { get; }
    public ImmutableArray<int> ResultWidths { get; }
    public LocationKind Location { get; init; }
    /// <summary>帧内变量序号，形参在前，局部在后。</summary>
    public int FrameSlot { get; init; }
    /// <summary>帧对象或写入的存储类型，观察值类型时按它的基本成员比较。</summary>
    public TypeShape? StorageType { get; init; }
    /// <summary>字段、被调方法或被初始化的类。</summary>
    public EntityRef? Entity { get; init; }
    public ExceptionKind Exception { get; init; }
    public RuntimeFunction Function { get; init; }
    /// <summary>调用的目标是第 0 个操作数。</summary>
    public bool Indirect { get; init; }
    /// <summary>类初始化的时机是精确的。</summary>
    public bool Precise { get; init; }
    /// <summary>读写字段：字段所属的类。</summary>
    public EntityRef? Owner { get; init; }
    /// <summary>调用：被调方法的形状（各形参与返回值的类别与存储位宽）。追溯与对照用，身份仍是 Entity。</summary>
    public MethodShape? Signature { get; init; }
    /// <summary>产生这个效果的目录项。</summary>
    public string Entry { get; }
    /// <summary>产生这个效果的指令在方法体里的偏移。</summary>
    public int Offset { get; }

    public TemplateEffect(EffectKind kind, ImmutableArray<Term> operands, ImmutableArray<int> resultWidths, string entry, int offset)
    {
        Kind = kind;
        Operands = operands;
        ResultWidths = resultWidths;
        Entry = entry;
        Offset = offset;
    }

    /// <summary>托管调用、写入、类初始化与新对象（含类初始化分量）改变托管可见的内存；运行时操作只动运行时私有的状态。</summary>
    public bool DefinesMemory => Kind is EffectKind.Write or EffectKind.Call or EffectKind.ClassInitialize or EffectKind.NewObject;

    public void WriteContent(DigestWriter writer)
    {
        writer.Write((int)Kind);
        if (Kind == EffectKind.FrameObject) writer.Write(FrameSlot);
        if (StorageType is { Kind: StackKind.Value } type)
        {
            writer.Write(type.StorageBits);
            writer.Write(type.Members.Length);
            foreach (var m in type.Members) { writer.Write(m.OffsetBits); writer.Write(m.Bits); }
        }
        writer.Write((int)Location);
        writer.Write((int)Exception);
        writer.Write((int)Function);
        writer.Write(Indirect ? 1 : 0);
        writer.Write(Precise ? 1 : 0);
        writer.Write(Entity is { } entity ? (int)entity.Kind : -1);
        writer.Write(Entity?.Key ?? 0L);
    }
}
