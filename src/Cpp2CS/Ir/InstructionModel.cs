using System.Collections.Immutable;
using System.Text.Json.Serialization;

namespace Cpp2CS.Ir;

public enum ExitKind { Next, Jump, Branch, Trap }
public enum ExceptionKind { ArmBreakpoint, X64Breakpoint, X64Debug, X64InvalidOpcode, X64GeneralProtection }
public sealed record ExceptionBoundary(ExceptionKind Kind, string Detail, ulong SavedAddress, ushort? Syndrome = null);

[JsonPolymorphic(TypeDiscriminatorPropertyName = "$kind")]
[JsonDerivedType(typeof(NextExit), "next")]
[JsonDerivedType(typeof(JumpExit), "jump")]
[JsonDerivedType(typeof(BranchExit), "branch")]
[JsonDerivedType(typeof(TrapExit), "trap")]
public abstract record MirExit
{
    private protected MirExit() { }
    [JsonRequired] public StateToken State { get; init; }
    [JsonIgnore] public ExitKind Kind => this switch
    {
        NextExit => ExitKind.Next, JumpExit => ExitKind.Jump,
        BranchExit => ExitKind.Branch, TrapExit => ExitKind.Trap,
        _ => throw new InvalidOperationException("Unknown MIR exit")
    };
    [JsonIgnore] public ulong Address => this is NextExit e ? e.NextAddress : 0;
    [JsonIgnore] public Value? Target => this switch { JumpExit e => e.Destination, BranchExit e => e.Taken, _ => null };
    [JsonIgnore] public Value? Condition => this is BranchExit e ? e.Predicate : null;
    [JsonIgnore] public Value? Alternative => this is BranchExit e ? e.NotTaken : null;
    [JsonIgnore] public string? Reason => this is TrapExit e ? e.Boundary.Detail : null;
    [JsonIgnore] public ulong? ResumeAddress => this is TrapExit e ? e.Boundary.SavedAddress : null;

    public static MirExit Next(ulong address) => new NextExit(address);
    public static MirExit Jump(Value target) => new JumpExit(target);
    public static MirExit Branch(Value condition, Value taken, Value notTaken) => new BranchExit(condition, taken, notTaken);
    public static MirExit Trap(ExceptionKind kind, string detail, ulong resumeAddress, ushort? syndrome = null) =>
        new TrapExit(new(kind, detail, resumeAddress, syndrome));
}
public sealed record NextExit(ulong NextAddress) : MirExit;
public sealed record JumpExit(Value Destination) : MirExit;
public sealed record BranchExit(Value Predicate, Value Taken, Value NotTaken) : MirExit;
public sealed record TrapExit(ExceptionBoundary Boundary) : MirExit;

public sealed record MirInstruction(Architecture Architecture, InstructionOrigin Origin, string Rule,
    ImmutableArray<Operation> Operations, MirExit Exit, ImmutableArray<SemanticObligation> Annotations, string ProfileId)
{
    [JsonIgnore] public StateToken FinalState => Exit.State;
    [JsonIgnore] public SupportClass Support => MirContracts.Support(this);
    [JsonIgnore] public ImmutableArray<SemanticObligation> Obligations => MirContracts.Obligations(this);
    [JsonIgnore] public ImmutableArray<string> Limitations => Obligations.Select(item => item.Reason).Distinct().ToImmutableArray();
}

public sealed record LiftResult(MirInstruction? Ir, string Form, string? Reason)
{
    public bool IsSupported => Ir is not null;
    public static LiftResult Supported(MirInstruction ir) => new(ir, ir.Rule, null);
    public static LiftResult Unsupported(string form, string reason) => new(null, form, reason);
}
