using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Targets.Frontend;

public sealed record Register(string Name, int Width);
public sealed record PreservedPart(Register Register, int Low, int Width);
public sealed record RegisterSlot(Register Register, AbstractSlot Slot, InputRole Role = InputRole.Argument);
/// <summary>入口 SP 是帧基址；实参区偏移分别相对入口及调用前 SP。CallerValues 的顺序给出稳定序号，包含全部保存单元和返回地址单元。</summary>
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
public interface IIndirectContext
{
    TermTable Terms { get; }
    // 返回块入口占位在唯一前驱出口的项；多前驱、入口或循环边界返回 null。
    Term? InUniquePredecessor(Term input);
    ImmutableArray<FlowCondition> Conditions { get; }
}
public interface IFlowFacts
{
    bool DoesNotReturn(CallTarget target);
    IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context);
}

/// <summary>指令读取的入口占位由共用层在组块和 SSA 时解析。</summary>
public interface IRegisterReader
{
    TermTable Terms { get; }
    Term Read(Register register);
}
/// <summary>地址为映像偏移。寄存器读写必须整单元；部分写入由 Slice/Concat 表达。</summary>
public interface IEmitter : IRegisterReader
{
    void Write(Register register, Term value);
    Term Load(Term address, int width);
    void Store(Term address, Term value);
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

/// <summary>异常边必须在 SSA 前加入图，包含调用前状态与处理入口定义；当前提升入口不接纳异常区间。</summary>
public interface IExceptionFlowProvider
{
    ImmutableArray<Cpp2CS.Native.Images.TryRegion> Regions { get; }
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
