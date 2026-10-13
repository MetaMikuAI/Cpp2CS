using System.Numerics;

namespace Cpp2CS.Ir;

public enum ExecutionOutcome { Normal, Trap, UnmodeledFaultStop, UnmodeledEnvironmentStop, UnmodeledSemanticsStop }
public enum StopKind { FaultBoundary, MissingEnvironment, UnmodeledSemantics }
public enum ChoicePolicy { ExplicitInputsThenZeroWitness }
public enum ExecutionStateKind { NormalSuccessor, CompletedPrefixWitness }

public sealed record ChoiceObservation(int Sequence, ulong InstructionAddress, int OperationIndex,
    Value Result, BigInteger Bits, bool IsExplicit);

// 已执行的前缀不表示异常交付后状态，也不承诺指令回滚。
public sealed record ExecutionStop(StopKind Kind, string Reason, int OperationIndex,
    StateToken CompletedStateToken, int MemoryEventStart, int MemoryEventCount);

public sealed record ExecutionResult
{
    public ExecutionOutcome Status { get; }
    public ulong? NextAddress { get; }
    public int Choices { get; }
    public StateToken CompletedStateToken { get; }
    public ExecutionStop? Stop { get; }
    public ExceptionBoundary? Exception { get; }
    public ChoicePolicy ChoicePolicy => ChoicePolicy.ExplicitInputsThenZeroWitness;
    public string Outcome => Status.ToString();
    public int? FaultOperation => Stop?.OperationIndex;
    public string? Event => Stop?.Reason ?? Exception?.Detail;
    public ulong? ResumeAddress => Exception?.SavedAddress;
    public ExecutionStateKind StateKind => Status == ExecutionOutcome.Normal
        ? ExecutionStateKind.NormalSuccessor : ExecutionStateKind.CompletedPrefixWitness;

    private ExecutionResult(ExecutionOutcome status, ulong? nextAddress, int choices,
        StateToken completedStateToken, ExecutionStop? stop = null, ExceptionBoundary? exception = null)
    {
        Status = status;
        NextAddress = nextAddress;
        Choices = choices;
        CompletedStateToken = completedStateToken;
        Stop = stop;
        Exception = exception;
    }

    public static ExecutionResult Completed(ulong nextAddress, int choices, StateToken state) =>
        new(ExecutionOutcome.Normal, nextAddress, choices, state);

    public static ExecutionResult Stopped(ExecutionStop stop, int choices) =>
        new(new MemoryStop(stop.Kind, stop.Reason).Outcome, null, choices, stop.CompletedStateToken, stop);

    public static ExecutionResult Trapped(ExceptionBoundary boundary, int choices, StateToken state) =>
        new(ExecutionOutcome.Trap, null, choices, state, exception: boundary);
}

internal readonly record struct MemoryStop(StopKind Kind, string Reason)
{
    public ExecutionOutcome Outcome => Kind switch
    {
        StopKind.FaultBoundary => ExecutionOutcome.UnmodeledFaultStop,
        StopKind.MissingEnvironment => ExecutionOutcome.UnmodeledEnvironmentStop,
        StopKind.UnmodeledSemantics => ExecutionOutcome.UnmodeledSemanticsStop,
        _ => throw new InvalidOperationException("Unknown execution stop kind")
    };
}

internal readonly record struct MemoryEffectResult(BigInteger Value = default, MemoryStop? Stop = null);
