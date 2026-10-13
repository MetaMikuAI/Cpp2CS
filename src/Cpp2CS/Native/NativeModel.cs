using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public readonly record struct ValueId(int Id);

public abstract record NativeType
{
    private protected NativeType() { }
}

public sealed record BitsType(int Width) : NativeType;
public sealed record WorldType : NativeType
{
    public static readonly WorldType Instance = new();
}

public readonly record struct NativeValue(ValueId Id, NativeType Type);
public sealed record BlockParameter(NativeValue Value, string? Slot);
public sealed record WorldFlow(NativeValue Input, NativeValue Output);
public sealed record MirOperationLocation(InstructionOrigin Origin, int OperationIndex);

public sealed record StateMap(ImmutableDictionary<string, NativeValue> Slots, NativeValue World);

public sealed record NativeNode(OpCode Code, NativeValue? Result, ImmutableArray<NativeValue> Inputs,
    OperationPayload Payload, WorldFlow? Flow, MirOperationLocation Source);

// 每个 MIR 操作保留一个阶段；槽读写没有执行节点，但仍有前后状态。
public sealed record NativeStep(int OperationIndex, int? NodeIndex, NativeValue? Result,
    StateMap Before, StateMap After);

public abstract record NativeDestination
{
    private protected NativeDestination() { }
}

public sealed record NativeAddressDestination(ulong Address) : NativeDestination;
public sealed record NativeValueDestination(NativeValue Target) : NativeDestination;
public sealed record NativeExceptionDestination(ExceptionBoundary Boundary) : NativeDestination;
public sealed record NativeCondition(NativeValue Value, bool RequiredValue);

public sealed record NativeEdge(RegionEdge Source, NativeDestination Destination,
    NativeCondition? Condition, StateMap State, ImmutableArray<NativeValue> Arguments)
{
    public EdgeId Id => Source.Id;
    public BlockId? Target => Source.Target;
}

public sealed record NativeBlock(RegionBlock Source, ImmutableArray<BlockParameter> Parameters,
    ImmutableArray<NativeNode> Nodes, ImmutableArray<NativeStep> Steps, StateMap InitialState,
    StateMap FinalState, ImmutableArray<NativeEdge> Edges)
{
    public BlockId Id => Source.Id;
    public MirCapabilities? Capabilities => Source.Instruction is { } instruction ? MirContracts.Capabilities(instruction) : null;
}

public sealed record NativeRegion(RegionRevision Source, ImmutableArray<NativeBlock> Blocks);
