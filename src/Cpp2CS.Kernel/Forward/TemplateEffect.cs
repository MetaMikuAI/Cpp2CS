using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Kernel.Forward;

/// <summary>模板一侧的效果的种类。</summary>
public enum EffectKind : byte { Read, Write, Call, RuntimeCall, ClassInitialize, ThrowIf }

/// <summary>
/// 模板一侧的一个效果：目录项的效果模板里的一步，形参已经换成实参。
/// 操作数的次序：读——位置的基；写——位置的基，然后是被写的值；调用——间接调用的目标（如果有），然后是各实参；
/// 条件抛出——条件。Entry 与 Offset 是追溯信息，不作身份，不进入摘要。
/// </summary>
public sealed class TemplateEffect : IFlowOccurrence
{
    public EffectKind Kind { get; }
    public ImmutableArray<Term> Operands { get; }
    public ImmutableArray<int> ResultWidths { get; }
    public LocationKind Location { get; init; }
    /// <summary>字段、被调方法或被初始化的类。</summary>
    public EntityRef? Entity { get; init; }
    public ExceptionKind Exception { get; init; }
    public RuntimeFunction Function { get; init; }
    /// <summary>调用的目标是第 0 个操作数。</summary>
    public bool Indirect { get; init; }
    /// <summary>类初始化的时机是精确的。</summary>
    public bool Precise { get; init; }
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

    /// <summary>托管调用、写入与类初始化改变托管可见的内存；运行时操作只动运行时私有的状态。</summary>
    public bool DefinesMemory => Kind is EffectKind.Write or EffectKind.Call or EffectKind.ClassInitialize;

    public void WriteContent(DigestWriter writer)
    {
        writer.Write((int)Kind);
        writer.Write((int)Location);
        writer.Write((int)Exception);
        writer.Write((int)Function);
        writer.Write(Indirect ? 1 : 0);
        writer.Write(Precise ? 1 : 0);
        writer.Write(Entity is { } entity ? (int)entity.Kind : -1);
        writer.Write(Entity?.Key ?? 0L);
    }
}
