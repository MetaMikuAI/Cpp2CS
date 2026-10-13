using System.Collections.Immutable;

namespace Cpp2CS.Ir;

public enum SlotAccessKind { Read, Write }
public sealed record StateAccess(int OperationIndex, SlotAccessKind Kind, string Slot, int Width, Value Value, StateFlow Flow);
public sealed record EffectAccess(int OperationIndex, OpCode Code, OperationEffects Effects, StateFlow Flow,
    Value? Result, ImmutableArray<Value> Inputs, OperationPayload Payload);
public enum SuccessorKind { Fallthrough, Jump, BranchTaken, BranchNotTaken, ExceptionBoundary }
public abstract record SuccessorDestination
{
    private protected SuccessorDestination() { }
}
public sealed record AddressDestination(ulong Address) : SuccessorDestination;
public sealed record ValueDestination(Value Target) : SuccessorDestination;
public sealed record ExceptionDestination(ExceptionBoundary Boundary) : SuccessorDestination;
public sealed record SuccessorCondition(Value Value, bool RequiredValue);
public sealed record MirSuccessor(SuccessorKind Kind, SuccessorDestination Destination,
    SuccessorCondition? Condition, StateToken State, TransferHint TransferHint = TransferHint.None);
public sealed record MirInstructionView(InstructionOrigin Origin, string Rule, MachineProfile Profile,
    ImmutableArray<StateAccess> StateAccesses, ImmutableArray<EffectAccess> Effects,
    ImmutableArray<MirSuccessor> Successors, MirCapabilities Capabilities);

// 上层从经过验证的 MIR 查询依赖，不再按助记符重建机器语义。
public static class MirInspection
{
    public static MirInstructionView Describe(MirInstruction ir)
    {
        var errors = MirValidator.Validate(ir);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        var state = ImmutableArray.CreateBuilder<StateAccess>();
        var effects = ImmutableArray.CreateBuilder<EffectAccess>();
        for (var index = 0; index < ir.Operations.Length; index++)
        {
            var op = ir.Operations[index];
            var spec = OperationSpecs.For(op.Code);
            if (op.Code is OpCode.ReadSlot or OpCode.WriteSlot)
            {
                var value = op.Code == OpCode.ReadSlot ? op.Result!.Value : op.Inputs[0];
                state.Add(new(index, op.Code == OpCode.ReadSlot ? SlotAccessKind.Read : SlotAccessKind.Write,
                    op.Slot!, value.Width, value, op.Flow!));
            }
            if (spec.HasStateFlow)
                effects.Add(new(index, op.Code, OperationSpecs.EffectiveEffects(op), op.Flow!, op.Result, op.Inputs, op.Payload));
        }
        var successors = ir.Exit switch
        {
            NextExit e => ImmutableArray.Create(new MirSuccessor(SuccessorKind.Fallthrough,
                new AddressDestination(e.NextAddress), null, e.State)),
            JumpExit e => ImmutableArray.Create(new MirSuccessor(SuccessorKind.Jump,
                new ValueDestination(e.Destination), null, e.State, e.TransferHint)),
            BranchExit e => ImmutableArray.Create(
                new MirSuccessor(SuccessorKind.BranchTaken, new ValueDestination(e.Taken), new(e.Predicate, true), e.State),
                new MirSuccessor(SuccessorKind.BranchNotTaken, new ValueDestination(e.NotTaken), new(e.Predicate, false), e.State)),
            TrapExit e => ImmutableArray.Create(new MirSuccessor(SuccessorKind.ExceptionBoundary,
                new ExceptionDestination(e.Boundary), null, e.State)),
            _ => throw new InvalidOperationException("Unknown MIR exit")
        };
        return new(ir.Origin, ir.Rule, MachineProfile.For(ir.Architecture), state.ToImmutable(),
            effects.ToImmutable(), successors, MirContracts.Capabilities(ir));
    }
}
