using Cpp2CS.Native.Images;
using System.Collections.Immutable;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Native;

/// <summary>身份只由对象本身决定；复制时保留来源，不以地址或显示编号充当身份。</summary>
public abstract class StableIdentity
{
    private protected StableIdentity(StableIdentity? origin) => Origin = origin;
    public StableIdentity? Origin { get; }
}
public sealed class CallIdentity(CallIdentity? origin = null) : StableIdentity(origin);
public sealed class MergeIdentity(MergeIdentity? origin = null) : StableIdentity(origin);
public sealed class FrameIdentity(FrameIdentity? origin = null) : StableIdentity(origin);
public sealed class WriteIdentity(WriteIdentity? origin = null) : StableIdentity(origin);
public sealed class ReadIdentity(ReadIdentity? origin = null) : StableIdentity(origin);
public sealed class FenceIdentity(FenceIdentity? origin = null) : StableIdentity(origin);
public sealed class TrapIdentity(TrapIdentity? origin = null) : StableIdentity(origin);
public sealed class BlockIdentity(BlockIdentity? origin = null) : StableIdentity(origin);

/// <summary>ArgumentArea 保留给 ABI 分类，不允许作为带值的入口、调用或返回槽。</summary>
public enum SlotKind { Integer, Floating, ArgumentArea, IndirectResult }
/// <summary>Position 为槽序号或实参区字节偏移；间接结果槽的 Position 为零。</summary>
public readonly record struct AbstractSlot(SlotKind Kind, long Position = 0);
public enum InputRole { Argument, MethodInformation, IndirectResult }
/// <summary>入口时调用方保留的位型；序号由目标的有序约定给出。</summary>
public sealed record CallerValue(int Index) : AtomIdentity
{
    public override string StableText => $"caller.{Index}";
}
public sealed record EntryAtom(AbstractSlot Slot) : AtomIdentity
{
    public override string StableText => $"entry.{Slot.Kind}.{Slot.Position}";
}
public sealed record ResultAtom(StableIdentity Definition, int Index = 0) : AtomIdentity
{
    public override string StableText => $"result.{Definition.GetType().Name}.{Index}";
}
/// <summary>入口帧基址、映像基址、线程指针各只有一个无名原子；其他地址由上层分类。</summary>
public sealed record RootAtom(AddressRoot Kind) : AtomIdentity
{
    public override string StableText => $"root.{Kind}";
}
public sealed record ExceptionAtom(BlockIdentity Handler) : AtomIdentity
{
    public override string StableText => "exception";
}
public enum AddressRoot { Frame, Image, Thread }
public sealed record SelectorAtom(BlockIdentity Handler) : AtomIdentity
{
    public override string StableText => "selector";
}
public sealed record EntryInput(AbstractSlot Slot, Term Value, InputRole Role = InputRole.Argument);
public sealed record SlotValue(AbstractSlot Slot, Term Value);
/// <summary>仅给出入口帧基址；静态帧对象与生存期由状态模型划分。</summary>
public sealed record FrameDescription(Term Base);
public sealed record Incoming(BlockIdentity Predecessor, Term Value);
public sealed record Merge(MergeIdentity Identity, Term Result, ImmutableArray<Incoming> Inputs);
/// <summary>Exception 和 Selector 都由本处理入口定义；Selector 表示匹配到的子句选择值。</summary>
public sealed record HandlerEntry(Term Exception, Term Selector, ImmutableArray<ExceptionClause> Clauses);
public sealed record Trace(ulong NativeAddress);

public abstract record CallTarget { private protected CallTarget() { } }
/// <summary>函数入口相对映像基址的字节偏移；托管候选身份由代码地图提供。</summary>
public sealed record ImageFunction(ulong EntryOffset) : CallTarget;
public sealed record ImportedTarget(ImportSymbol Symbol) : CallTarget;
public sealed record ComputedTarget(Term Value) : CallTarget;

public abstract record Statement
{
    private protected Statement() { }
    public Trace? Trace { get; init; }
}
public sealed record MemoryRead(ReadIdentity Identity, Term Address, int Width, Term Result) : Statement
{
    public bool Acquire { get; init; }
}
public sealed record MemoryWrite(WriteIdentity Identity, Term Address, int Width, Term Value) : Statement
{
    public bool Release { get; init; }
}
/// <summary>ReadWrite 约束读写到读写，Read 约束读到读写，Write 约束写到写。</summary>
public enum FenceOrdering { ReadWrite, Read, Write }
/// <summary>域内的先行访问先于后续访问被观察；Domain 由目标描述定义，不表示等待访问完成。</summary>
public sealed record MemoryFence(FenceIdentity Identity, string Domain) : Statement
{
    public FenceOrdering Ordering { get; init; }
}
/// <summary>条件为真时是硬件陷阱的结局，其后的语句只在条件为假时执行。指令内部的条件陷阱不拆块。</summary>
public sealed record TrapWhen(TrapIdentity Identity, Term Condition) : Statement;
/// <summary>尾调用表示为调用加返回。没有展开边仅表示本函数内没有处理入口；是否可能抛出由被调效果回答。</summary>
public sealed record Call(CallIdentity Identity, CallTarget Target, ImmutableArray<SlotValue> Arguments,
    ImmutableArray<SlotValue> Results, bool DoesNotReturn = false, BlockIdentity? Unwind = null, Term? OutgoingArgumentArea = null) : Statement;
public sealed record DynamicAllocation(FrameIdentity Identity, Term Size, int Alignment, Term Result) : Statement;

public abstract record Terminator { private protected Terminator() { } }
public sealed record Jump(BlockIdentity Target) : Terminator;
public sealed record Branch(Term Condition, BlockIdentity True, BlockIdentity False) : Terminator;
public sealed record SwitchCase(System.Numerics.BigInteger Value, BlockIdentity Target);
public sealed record JumpTable(Term Selector, ImmutableArray<SwitchCase> Cases, BlockIdentity Default) : Terminator;
public sealed record Return(ImmutableArray<SlotValue> Results) : Terminator;
public sealed record ResumeUnwind(Term Exception) : Terminator;
public sealed record Unreachable : Terminator;

public sealed record Block(BlockIdentity Identity, ImmutableArray<Merge> Merges,
    ImmutableArray<Statement> Statements, Terminator End, HandlerEntry? Handler = null)
{
    public Trace? Trace { get; init; }
}

/// <summary>集合和图不可变；项表可以继续驻留新项，不会改变已有快照。</summary>
public sealed class NativeFunction
{
    internal NativeFunction(TermTable terms, BlockIdentity entry, int addressWidth,
        ImmutableArray<EntryInput> inputs, FrameDescription frame, Term? imageBase, Term? threadPointer, Term? incomingArgumentArea,
        ImmutableArray<Block> blocks)
    {
        Terms = terms;
        Entry = entry;
        AddressWidth = addressWidth;
        Inputs = inputs;
        Frame = frame;
        ImageBase = imageBase;
        ThreadPointer = threadPointer;
        IncomingArgumentArea = incomingArgumentArea;
        Blocks = blocks;
    }
    public TermTable Terms { get; }
    public BlockIdentity Entry { get; }
    public int AddressWidth { get; }
    public ImmutableArray<EntryInput> Inputs { get; }
    public FrameDescription Frame { get; }
    public Term? ImageBase { get; }
    public Term? ThreadPointer { get; }
    /// <summary>传入栈实参区的地址表达式，在入口可用；内容由状态模型读取。</summary>
    public Term? IncomingArgumentArea { get; }
    public ImmutableArray<Block> Blocks { get; }
}

/// <summary>Freeze 复制集合，允许调用者继续搭建另一份快照；契约错误由出口检查器汇总。</summary>
public sealed class FunctionBuilder(TermTable terms, BlockIdentity entry, int addressWidth, FrameDescription frame)
{
    public List<EntryInput> Inputs { get; } = [];
    public Term? ImageBase { get; set; }
    public Term? ThreadPointer { get; set; }
    public Term? IncomingArgumentArea { get; set; }
    public List<Block> Blocks { get; } = [];
    public NativeFunction Freeze() => new(terms, entry, addressWidth, Inputs.ToImmutableArray(), frame,
        ImageBase, ThreadPointer, IncomingArgumentArea, Blocks.ToImmutableArray());
}
