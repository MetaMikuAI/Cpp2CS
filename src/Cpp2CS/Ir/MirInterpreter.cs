using System.Numerics;

namespace Cpp2CS.Ir;

public sealed class MachineState
{
    public Dictionary<string, BigInteger> Slots { get; } = [];
    public Dictionary<ulong, byte> Memory { get; } = [];
    public List<string> Accesses { get; } = [];
    public List<WorldEvent> Events { get; } = [];
    public ExclusiveReservation? Reservation { get; set; }
    public Queue<bool> ExclusiveStoreDecisions { get; } = new();
    public Queue<ScheduledMemoryEvent> Schedule { get; } = new();
    public List<ScheduledMemoryEvent> AppliedSchedule { get; } = [];
    public Dictionary<ulong, bool> WritePermissions { get; } = [];
    public Dictionary<ulong, bool> CodeGuardedPages { get; } = [];
    public Queue<BigInteger> ChoiceInputs { get; } = new();
    public List<ChoiceObservation> ChoiceObservations { get; } = [];
    public BigInteger ReadSlot(string slot) => Slots[slot];
}

// 用于具体验证；未显式给出的 Undefined 取零仅代表一个执行见证。
public static class MirInterpreter
{
    public static BigInteger Mask(int width) => MirOperationEvaluator.Mask(width);
    public static BigInteger Signed(BigInteger bits, int width) => MirOperationEvaluator.Signed(bits, width);

    public static ExecutionResult Execute(MirInstruction ir, MachineState state, Action<Value, BigInteger>? observeValue = null)
    {
        var errors = MirValidator.Validate(ir);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        var values = new BigInteger[ir.Operations.Length];
        var inputs = new BigInteger[4];
        var choices = 0;
        var completedState = new StateToken(0);
        for (var index = 0; index < ir.Operations.Length; index++)
        {
            var op = ir.Operations[index];
            var operationEventStart = state.Events.Count;
            for (var i = 0; i < op.Inputs.Length; i++) inputs[i] = values[op.Inputs[i].Id];
            var evaluation = MirOperationEvaluator.Evaluate(ir.Architecture, op, inputs.AsSpan(0, op.Inputs.Length), state, ir.Origin, index);
            choices += evaluation.Choices;
            if (evaluation.Stop is { } stop)
                return ExecutionResult.Stopped(new(stop.Kind, stop.Reason, index, completedState,
                    operationEventStart, state.Events.Count - operationEventStart), choices);
            if (op.Result is { } result)
            {
                values[result.Id] = evaluation.Bits;
                observeValue?.Invoke(result, evaluation.Bits);
            }
            if (op.Flow is { } flow) completedState = flow.Output;
        }
        var exit = ir.Exit;
        var next = exit.Kind switch
        {
            ExitKind.Next => exit.Address,
            ExitKind.Jump => (ulong)values[exit.Target!.Value.Id],
            ExitKind.Branch => (ulong)values[(values[exit.Condition!.Value.Id] != 0 ? exit.Target : exit.Alternative)!.Value.Id],
            _ => (ulong?)null
        };
        return exit is TrapExit trap ? ExecutionResult.Trapped(trap.Boundary, choices, completedState)
            : ExecutionResult.Completed(next!.Value, choices, completedState);
    }
}
