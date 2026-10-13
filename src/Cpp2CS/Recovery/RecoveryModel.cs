using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public enum MachineAbiKind { Aapcs64, WindowsX64 }
public enum RecoveryScalarKind { Integer, Address, Float }
public sealed record RecoveryScalarType(int Width, RecoveryScalarKind Kind = RecoveryScalarKind.Integer);
public sealed record FunctionSignature(ImmutableArray<RecoveryScalarType> Arguments, RecoveryScalarType? Result);

// 这些是采用的逻辑调用合同，不能由函数名称或机器调用提示推断。
public sealed record FunctionEffects(bool ReadsMemory = true, bool WritesMemory = true,
    bool ExternalEffects = true, bool MayThrow = true, bool MayReturn = true,
    bool MayDiverge = true, bool MayTerminate = true);
public sealed record FunctionRecoveryDomain(bool NormalExecution, bool ValidPrivateFrame,
    bool StableThreadEnvironment = false, bool SequentialMemory = false);
public sealed record FunctionContract(string Name, ulong EntryAddress, FunctionSignature Signature,
    MachineAbiKind Abi, FunctionEffects Effects, ImmutableArray<string> Assumptions,
    FunctionRecoveryDomain? Domain = null);

public abstract record MachineArgumentLocation(int Width);
public sealed record SlotArgumentLocation(string Slot, int Offset, int BitWidth) : MachineArgumentLocation(BitWidth);
// 偏移以机器调用准备完成后的被调入口 SP 为基准。
public sealed record StackArgumentLocation(long EntrySpOffset, int BitWidth) : MachineArgumentLocation(BitWidth);
public sealed record MachineInterface(ImmutableArray<MachineArgumentLocation> Arguments,
    SlotArgumentLocation? Result, string StackPointer, int StackAlignment, int NormalReturnSpAdjustment);

public enum SlotRelationKind { Preserve, Havoc, Result, AddConstant, Constant }
public sealed record MachineSlotSegment(int Offset, int Width, SlotRelationKind Kind,
    string? InputSlot = null, int InputOffset = 0, long Constant = 0);
public sealed record MachineSlotRelation(string Slot, int Width, ImmutableArray<MachineSlotSegment> Segments);
public sealed record MachineSlotRead(string Slot, int Offset, int Width);
// 即使逻辑合同是纯函数，被调体仍可修改自己的栈、入栈实参及 Windows shadow space。
public sealed record MachineWorldRelation(bool ReadsWorld, bool WritesProgramMemory,
    bool ExternalEffects, bool MayWritePrivateStack);
public enum MachineCallOutcomeKind { Unwind, Terminate, Diverge }
public sealed record MachineCallOutcome(MachineCallOutcomeKind Kind,
    ImmutableArray<MachineSlotRelation> Outputs, MachineWorldRelation World);
public sealed record MachineCallSummary(FunctionContract Callee, MachineInterface Interface,
    ImmutableArray<MachineSlotRead> Reads, ImmutableArray<MachineSlotRelation> NormalOutputs,
    MachineWorldRelation World, ImmutableArray<string> Prerequisites,
    ImmutableArray<MachineCallOutcome> OtherOutcomes);

public enum RecoveryGapKind
{
    Decode, Budget, UnknownCallTarget, MissingCallContract, UnsupportedInterface,
    UnknownJumpTarget, UnclassifiedTailCall, UnmodeledException, ContractConflict
}
public sealed record RecoveryGap(ulong Address, RecoveryGapKind Kind, string Reason);
public enum DerivedEdgeKind { Direct, Call, Return, TailCall, Gap, Exception }
public sealed record DerivedFunctionEdge(int Id, int SourceBlock, MirSuccessor Source,
    DerivedEdgeKind Kind, int? TargetBlock, ulong? MachineTarget,
    MachineCallSummary? Call, ulong? Continuation, RecoveryGap? Gap, bool IsTailCandidate = false);
public sealed record DerivedFunctionBlock(int Id, ulong Address, MirInstruction? Instruction,
    ImmutableArray<DerivedFunctionEdge> Edges, RecoveryGap? Gap);

// 派生图保留原 MIR 出口；摘要的正常结果边不会改写原调用目标。
public sealed record DerivedFunctionGraph(string Revision, string ImageId, Architecture Architecture,
    FunctionContract Contract, ImmutableArray<DerivedFunctionBlock> Blocks,
    ImmutableArray<RecoveryGap> Gaps, ImmutableArray<string> Dependencies)
{
    // 仅表示发现图与采用的调用合同闭合；返回协议等价仍由语义投影验证。
    public bool IsClosed => Gaps.IsEmpty;
    public DerivedFunctionBlock Entry => Blocks.Single(block => block.Address == Contract.EntryAddress);
}

public sealed record FunctionGraphOptions(int MaxInstructions = 10_000,
    ImmutableDictionary<ulong, string>? TailCallEvidence = null,
    ImmutableDictionary<ulong, ulong>? IndirectCallTargets = null,
    bool InferTailCallCandidates = false);
