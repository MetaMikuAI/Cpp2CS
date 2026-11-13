using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Targets.Frontend;

public sealed record Register(string Name, int Width);
public sealed record PreservedPart(Register Register, int Low, int Width);
public sealed record RegisterSlot(Register Register, AbstractSlot Slot, InputRole Role = InputRole.Argument);
/// <summary>入口 SP 是帧基址；实参区偏移分别相对入口及调用前 SP。CallerValues 的顺序给出稳定序号，包含全部保存单元；返回地址在寄存器里的目标把该寄存器也列入，在栈上的目标不为它设调用方的值，返回指令的弹栈由 ReturnStackOffset 表达。</summary>
public sealed record RegisterConvention(
    ImmutableArray<RegisterSlot> Arguments, ImmutableArray<RegisterSlot> Results,
    ImmutableHashSet<Register> Preserved, Register StackPointer,
    long IncomingAreaOffset, long OutgoingAreaOffset,
    ImmutableArray<Register> CallerValues)
{
    /// <summary>返回语义执行后的 SP 相对入口帧基址的偏移。</summary>
    public long ReturnStackOffset { get; init; }
    /// <summary>尾调用前的 SP 相对入口帧基址的偏移；不包含返回指令的弹栈。</summary>
    public long TailCallStackOffset { get; init; }
    /// <summary>只保存部分位的单元；不与 Preserved 重叠，未列出的位被调用破坏。</summary>
    public ImmutableArray<PreservedPart> PreservedParts { get; init; } = [];
}

/// <summary>解码失败返回原因；成功指令的语义只通过发射器构造项和效果。同一条指令的 Emit 可能被调用多次，结果只取决于发射器给出的值。</summary>
public interface IInstructionSet
{
    ImmutableArray<Register> Registers { get; }
    DecodeResult Decode(ulong address);
}
public sealed record Instruction(int Length, Action<IEmitter> Emit);
public sealed record DecodeResult(Instruction? Instruction, Reason? Failure);
public sealed record CallTargetResolution(CallTarget? Target, Reason? Failure);
/// <summary>链接器变换的逆向取指与调用入口归一；不改变映像中的函数范围。</summary>
public interface IInstructionFlowFacts
{
    DecodeResult DecodeForFlow(ulong address, Cpp2CS.Native.Images.FunctionRange range);
    CallTargetResolution ResolveCallTarget(CallTarget target);
}
public sealed record IndirectCase(BigInteger Value, ulong Target);
/// <summary>解析器持有映像，须证明映射或尾调用与目标项等价。</summary>
public abstract record IndirectResolution
{
    private protected IndirectResolution() { }
}
public sealed record IndirectTable(Term Selector, ImmutableArray<IndirectCase> Cases, ulong Default) : IndirectResolution;
public sealed record IndirectTailCall(Term Target) : IndirectResolution;
public sealed record IndirectUnknown(Reason Reason) : IndirectResolution;
public sealed record FlowCondition(Term Condition, bool IsTrue);
/// <summary>提供流事实解析使用的只读映像，不参与指令语义。</summary>
public interface IImageInstructionSet
{
    Cpp2CS.Native.Images.IImage Image { get; }
}

public interface IIndirectContext
{
    Cpp2CS.Native.Images.IImage? Image => null;
    Cpp2CS.Native.Images.FunctionRange? Range => null;
    /// <summary>按读取结果查询当前组块快照中的读取地址与位宽。</summary>
    MemoryRead? ReadOf(Term result) => null;
    ulong? EntryAddress => null;
    TermTable Terms { get; }
    // 返回块入口占位在唯一前驱出口的项；多前驱、入口或循环边界返回 null。
    Term? InUniquePredecessor(Term input);
    /// <summary>块入口占位在每个前驱出口的项，用来收集一个值的全部来源；不是块入口占位或该块没有前驱时为空。</summary>
    ImmutableArray<Term> InPredecessors(Term input) => [];
    ImmutableArray<FlowCondition> Conditions { get; }
}
public interface IFlowFacts
{
    bool DoesNotReturn(CallTarget target);
    bool ResumesUnwind(CallTarget target) => false;
    IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context);
}

/// <summary>目录身份与目标的寄存器异常模型分离；不改变不返回与间接转移的判定。</summary>
public sealed class ExceptionFlowFacts(IFlowFacts inner, Func<CallTarget, bool> resumesUnwind) : IFlowFacts
{
    public bool DoesNotReturn(CallTarget target) => inner.DoesNotReturn(target);
    public bool ResumesUnwind(CallTarget target) => inner.ResumesUnwind(target) || resumesUnwind(target);
    public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context) => inner.ResolveIndirect(address, target, context);
}

/// <summary>指令读取的入口占位由共用层在组块和 SSA 时解析。</summary>
public interface IRegisterReader
{
    TermTable Terms { get; }
    Term Read(Register register);
}
/// <summary>显式的同步访问能力；不能实现的消费者不得将其当作普通内存访问。</summary>
public interface IOrderedMemoryEmitter
{
    Term LoadAcquire(Term address, int width);
    void StoreRelease(Term address, Term value);
    void Fence(string domain, FenceOrdering ordering);
}

/// <summary>独占事件保留地址、数据与状态结果，不提供普通读写的语义。</summary>
public interface IExclusiveMemoryEmitter
{
    Term LoadExclusive(Term address, int width, bool acquire);
    Term StoreExclusive(Term address, Term value, bool release);
    void ClearExclusive();
}

/// <summary>地址为映像偏移。寄存器读写必须整单元；部分写入由 Slice/Concat 表达。</summary>
public interface IRegisterState : IRegisterReader
{
    void Write(Register register, Term value);
}
public interface IEmitter : IRegisterState
{
    Term Load(Term address, int width);
    void Store(Term address, Term value);
    /// <summary>条件（1 位）为真时是硬件陷阱；本条指令此后的语义只在条件为假时生效。</summary>
    void TrapIf(Term condition);
    void Call(CallTarget target);
    void Jump(ulong target);
    void Branch(Term condition, ulong whenTrue, ulong whenFalse);
    void IndirectJump(Term target);
    void Return();
    void Trap();
    Term ImageAddress(ulong offset);
    Term ThreadPointer { get; }
    void Fail(Reason reason);
}

/// <summary>可选观察器报告阶段完成；只用于调用方测量，不参与恢复判定。</summary>
public enum LiftPhase { Discovery, Composition, IndirectResolution, Ssa, ExitCheck }
public sealed record LiftFailure(ulong Address, Reason Reason);
public sealed record LiftResult(NativeFunction? Function, LiftFailure? Failure);

/// <summary>异常边在 SSA 前加入图；目标模型负责入口值及继续展开的实参归位。</summary>
public interface IExceptionFlowProvider
{
    ImmutableArray<Cpp2CS.Native.Images.TryRegion> Regions { get; }
    Cpp2CS.Native.Images.TryRegionIndex RegionIndex => new(Regions);
    IExceptionModel ExceptionModel { get; }
}
public interface IExceptionModel
{
    void EnterHandler(IRegisterState state, Term exception, Term selector);
    bool IsResumeUnwind(CallTarget target);
    Term ResumeException(IRegisterReader state);
}
/// <summary>动态分配识别在逐条语义后、SSA 前接入；Size 来自同一项表，结果须以显式帧身份定义。</summary>
public sealed record DynamicStackRequest(Term Size, int Alignment, Register Result);
public interface IDynamicStackProvider
{
    DynamicStackRequest? Describe(ulong address, IReadOnlyDictionary<Register, Term> state, TermTable terms);
}

internal sealed record RegisterInput(ulong Address, Register Register) : AtomIdentity
{
    public override string StableText => $"frontend.input.{Address:x}.{Register.Name}";
}
