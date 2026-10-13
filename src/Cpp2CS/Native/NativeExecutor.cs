using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public enum RegionRunOutcome { Transfer, AnalysisStop, Trap, ExecutionStop, Budget }
public sealed record RegionExecutionResult(RegionRunOutcome Outcome, ulong Address, ulong? NextAddress,
    RegionBoundary? Boundary, ExecutionResult? LastInstruction, int Instructions, ImmutableArray<EdgeId> TraversedEdges);

// 具体执行只验证指定输入与有限路径；开放出口不隐式执行被调过程。
public static class NativeExecutor
{
    public static RegionExecutionResult Execute(NativeRegion region, ulong entryAddress, MachineState state,
        int instructionBudget, Action<MirInstruction, ExecutionResult, MachineState>? observe = null)
    {
        var errors = NativeValidator.Validate(region);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        return ExecuteCore(region, entryAddress, state, instructionBudget, observe);
    }

    public static RegionExecutionResult Execute(NativeNormalizationResult normalized, ulong entryAddress, MachineState state,
        int instructionBudget, Action<MirInstruction, ExecutionResult, MachineState>? observe = null)
    {
        var errors = NativeNormalizationValidator.Validate(normalized);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        return ExecuteCore(normalized.Region, entryAddress, state, instructionBudget, observe);
    }

    private static RegionExecutionResult ExecuteCore(NativeRegion region, ulong entryAddress, MachineState state,
        int instructionBudget, Action<MirInstruction, ExecutionResult, MachineState>? observe)
    {
        if (instructionBudget < 1) throw new ArgumentOutOfRangeException(nameof(instructionBudget));
        var entry = region.Source.Entries.FirstOrDefault(e => e.Seed.Address == entryAddress)
            ?? throw new ArgumentException("Execution must start at an explicit region entry", nameof(entryAddress));
        var blocks = region.Blocks.ToDictionary(b => b.Id);
        var block = blocks[entry.Block];
        var bits = new Dictionary<ValueId, BigInteger?>();
        var worlds = new Dictionary<ValueId, long>();
        var prepared = region.Blocks.ToDictionary(b => b.Id, b => b.Nodes.Select(node =>
        {
            var original = b.Source.Instruction!.Operations[node.Source.OperationIndex];
            Value? result = node.Result is { } value ? new(original.Result!.Value.Id, ((BitsType)value.Type).Width) : null;
            return new Operation(node.Code, result,
                node.Inputs.Select((v, index) => new Value(index, ((BitsType)v.Type).Width)).ToImmutableArray(), node.Payload);
        }).ToArray());
        foreach (var parameter in block.Parameters)
        {
            if (parameter.Slot is { } slot)
                bits[parameter.Value.Id] = state.Slots.TryGetValue(slot, out var value) ? value : null;
            else worlds[parameter.Value.Id] = 0;
        }
        var traversed = ImmutableArray.CreateBuilder<EdgeId>();
        var instructions = 0;
        ExecutionResult? last = null;
        var arguments = new BigInteger[4];
        BigInteger Read(NativeValue value) => bits[value.Id]
            ?? throw new InvalidOperationException("An unknown input reached a value operation before its slot read");
        while (true)
        {
            if (block.Source.Stop is { } boundary)
                return new(RegionRunOutcome.AnalysisStop, block.Source.Address, null, boundary, last, instructions, traversed.ToImmutable());
            if (instructions == instructionBudget)
                return new(RegionRunOutcome.Budget, block.Source.Address, null, null, last, instructions, traversed.ToImmutable());
            var ir = block.Source.Instruction!;
            var completed = new StateToken(0);
            var choices = 0;
            ExecutionResult? stopped = null;
            foreach (var step in block.Steps)
            {
                var original = ir.Operations[step.OperationIndex];
                var eventStart = state.Events.Count;
                if (original.Code == OpCode.ReadSlot)
                {
                    var input = bits[step.Result!.Value.Id];
                    if (input is null)
                    {
                        stopped = ExecutionResult.Stopped(new(StopKind.MissingEnvironment,
                            $"state slot is required: {original.Slot}", step.OperationIndex, completed, eventStart, 0), choices);
                        break;
                    }
                    if (input < 0 || input > MirInterpreter.Mask(original.Result!.Value.Width))
                        throw new InvalidOperationException($"State slot exceeds declared width: {original.Slot}");
                }
                else if (original.Code == OpCode.WriteSlot)
                    state.Slots[original.Slot!] = Read(step.After.Slots[original.Slot!]);
                else if (step.NodeIndex is { } nodeIndex)
                {
                    var node = block.Nodes[nodeIndex];
                    for (var i = 0; i < node.Inputs.Length; i++) arguments[i] = Read(node.Inputs[i]);
                    var evaluated = MirOperationEvaluator.Evaluate(region.Source.Architecture, prepared[block.Id][nodeIndex],
                        arguments.AsSpan(0, node.Inputs.Length), state, ir.Origin, step.OperationIndex);
                    choices += evaluated.Choices;
                    if (evaluated.Stop is { } failure)
                    {
                        stopped = ExecutionResult.Stopped(new(failure.Kind, failure.Reason, step.OperationIndex,
                            completed, eventStart, state.Events.Count - eventStart), choices);
                        break;
                    }
                    if (node.Result is { } result) bits[result.Id] = evaluated.Bits;
                    if (node.Flow is { } flow) worlds[flow.Output.Id] = checked(worlds[flow.Input.Id] + 1);
                }
                if (original.Flow is { } originalFlow) completed = originalFlow.Output;
            }
            instructions++;
            if (stopped is not null)
            {
                observe?.Invoke(ir, stopped, state);
                return new(RegionRunOutcome.ExecutionStop, ir.Origin.Address, null, null, stopped, instructions, traversed.ToImmutable());
            }
            var edge = block.Edges.Single(e => e.Condition is not { } condition || (Read(condition.Value) != 0) == condition.RequiredValue);
            ulong? next = edge.Destination switch
            {
                NativeAddressDestination address => address.Address,
                NativeValueDestination target => (ulong)Read(target.Target),
                NativeExceptionDestination => null,
                _ => throw new InvalidOperationException("Unknown native destination")
            };
            last = edge.Destination is NativeExceptionDestination exception
                ? ExecutionResult.Trapped(exception.Boundary, choices, completed)
                : ExecutionResult.Completed(next!.Value, choices, completed);
            observe?.Invoke(ir, last, state);
            traversed.Add(edge.Id);
            if (edge.Target is not { } targetBlock)
                return new(last.Status == ExecutionOutcome.Trap ? RegionRunOutcome.Trap : RegionRunOutcome.Transfer,
                    ir.Origin.Address, next, edge.Source.Boundary, last, instructions, traversed.ToImmutable());
            var successor = blocks[targetBlock];
            // 先捕获全部边实参，再绑定参数，避免回边覆盖尚未读取的值。
            var incoming = edge.Arguments.Select(v => v.Type is WorldType ? null : bits[v.Id]).ToArray();
            var incomingWorld = worlds[edge.State.World.Id];
            for (var i = 0; i < successor.Parameters.Length; i++)
            {
                var parameter = successor.Parameters[i];
                if (parameter.Value.Type is WorldType) worlds[parameter.Value.Id] = incomingWorld;
                else bits[parameter.Value.Id] = incoming[i];
            }
            block = successor;
        }
    }
}

// 对照路径直接执行原 MIR；不使用 SSA 的值或状态映射。
public static class MirRegionExecutor
{
    public static RegionExecutionResult Execute(RegionRevision region, ulong entryAddress, MachineState state,
        int instructionBudget, Action<MirInstruction, ExecutionResult, MachineState>? observe = null)
    {
        var errors = RegionValidator.Validate(region);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        if (instructionBudget < 1) throw new ArgumentOutOfRangeException(nameof(instructionBudget));
        var entry = region.Entries.FirstOrDefault(e => e.Seed.Address == entryAddress)
            ?? throw new ArgumentException("Execution must start at an explicit region entry", nameof(entryAddress));
        var blocks = region.Blocks.ToDictionary(b => b.Id);
        var block = blocks[entry.Block];
        var traversed = ImmutableArray.CreateBuilder<EdgeId>();
        var instructions = 0;
        ExecutionResult? last = null;
        while (true)
        {
            if (block.Stop is { } boundary)
                return new(RegionRunOutcome.AnalysisStop, block.Address, null, boundary, last, instructions, traversed.ToImmutable());
            if (instructions == instructionBudget)
                return new(RegionRunOutcome.Budget, block.Address, null, null, last, instructions, traversed.ToImmutable());
            var ir = block.Instruction!;
            bool? taken = null;
            last = MirInterpreter.Execute(ir, state, (value, actual) =>
            {
                if (ir.Exit.Condition == value) taken = actual != 0;
            });
            instructions++;
            observe?.Invoke(ir, last, state);
            if (last.Status is not (ExecutionOutcome.Normal or ExecutionOutcome.Trap))
                return new(RegionRunOutcome.ExecutionStop, block.Address, null, null, last, instructions, traversed.ToImmutable());
            var edge = block.Edges.Single(e => e.Successor.Condition is not { } condition || taken == condition.RequiredValue);
            traversed.Add(edge.Id);
            if (edge.Target is not { } target)
                return new(last.Status == ExecutionOutcome.Trap ? RegionRunOutcome.Trap : RegionRunOutcome.Transfer,
                    block.Address, last.NextAddress, edge.Boundary, last, instructions, traversed.ToImmutable());
            block = blocks[target];
        }
    }
}
