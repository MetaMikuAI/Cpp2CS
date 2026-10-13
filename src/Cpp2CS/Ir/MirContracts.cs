using System.Collections.Immutable;

namespace Cpp2CS.Ir;

public enum ObligationKind
{
    FaultDelivery, EnvironmentInput, ConcurrentExecutions, MonitorGranule,
    CacheEffects, UnmodeledSemantics, PartialState
}
public sealed record SemanticObligation(ObligationKind Kind, string Reason, int? OperationIndex = null);
public sealed record MirCapabilities(SupportClass Support, bool NormalTransitionRepresented,
    bool ExceptionBoundaryRepresented, bool MayStopBeforeExit, bool HasChoices,
    bool FaultDeliveryModeled, bool ConcurrentExecutionsVerified, ImmutableArray<SemanticObligation> Obligations);

// 能力由操作和出口推导；附注只能增加义务，不能撤销核心操作的义务。
public static class MirContracts
{
    public static SupportClass Support(MirInstruction ir)
    {
        if (ir.Exit is TrapExit) return SupportClass.ExceptionBoundaryOnly;
        if (!ir.Annotations.IsEmpty || ir.Operations.Any(op => OperationSpecs.For(op.Code).HasResidual))
            return SupportClass.NormalPathOnly;
        return SupportClass.Exact;
    }

    public static ImmutableArray<SemanticObligation> Obligations(MirInstruction ir)
    {
        var result = ImmutableArray.CreateBuilder<SemanticObligation>();
        result.AddRange(ir.Annotations);
        for (var index = 0; index < ir.Operations.Length; index++)
        {
            var op = ir.Operations[index];
            void Add(ObligationKind kind, string reason) => result.Add(new(kind, reason, index));
            switch (op.Code)
            {
                case OpCode.Guard:
                    var guard = (GuardPayload)op.Payload;
                    Add(guard.Kind switch
                    {
                        StopKind.FaultBoundary => ObligationKind.FaultDelivery,
                        StopKind.MissingEnvironment => ObligationKind.EnvironmentInput,
                        StopKind.UnmodeledSemantics => ObligationKind.UnmodeledSemantics,
                        _ => throw new InvalidOperationException("Unknown guard stop kind")
                    }, guard.Reason);
                    break;
                case OpCode.CodeGuarded:
                    Add(ObligationKind.EnvironmentInput, "guarded-page attributes require an explicit environment input");
                    Add(ObligationKind.FaultDelivery, "branch-target fault delivery is unmodeled");
                    break;
                case OpCode.Load:
                case OpCode.Store:
                case OpCode.LoadIf:
                case OpCode.StoreIf:
                case OpCode.LoadExclusive:
                case OpCode.StoreExclusive:
                    Add(ObligationKind.FaultDelivery, "memory fault delivery and partial architectural state are unmodeled");
                    if (op.Memory is { Order: not MemoryOrder.Relaxed } or { AtomicWidth: > 0 } ||
                        op.Code is OpCode.LoadExclusive or OpCode.StoreExclusive)
                        Add(ObligationKind.ConcurrentExecutions, "ordered events describe one concrete execution, not all concurrent executions");
                    if (op.Memory is { NonTemporal: true })
                        Add(ObligationKind.CacheEffects, "non-temporal cache effects are outside the byte-state model");
                    if (op.Code is OpCode.LoadExclusive or OpCode.StoreExclusive)
                        Add(ObligationKind.MonitorGranule, "implementation monitor granules are unmodeled");
                    if (op.Code == OpCode.StoreExclusive)
                        Add(ObligationKind.EnvironmentInput, "exclusive-store success requires an external monitor decision");
                    break;
                case OpCode.AtomicRmw:
                    Add(ObligationKind.FaultDelivery, "locked RMW fault delivery and partial architectural state are unmodeled");
                    Add(ObligationKind.EnvironmentInput, "locked RMW requires explicit write permissions");
                    Add(ObligationKind.ConcurrentExecutions, "one indivisible event does not prove complete concurrent executions");
                    break;
                case OpCode.ClearExclusive:
                    Add(ObligationKind.MonitorGranule, "implementation monitor granules are unmodeled");
                    break;
                case OpCode.Barrier:
                    Add(ObligationKind.ConcurrentExecutions, "barrier ordering is retained; the interpreter is not a weak-memory solver");
                    break;
                case OpCode.Prefetch:
                    Add(ObligationKind.CacheEffects, "prefetch cache effects are outside the byte-state model");
                    break;
                case OpCode.WriteProbe:
                    Add(ObligationKind.EnvironmentInput, "write-access probing requires explicit permissions");
                    Add(ObligationKind.FaultDelivery, "write-access fault delivery is unmodeled");
                    break;
            }
        }
        if (ir.Exit is TrapExit)
            result.Add(new(ObligationKind.FaultDelivery, "exception event and saved address are represented; delivery and handler state are unmodeled"));
        return result.ToImmutable();
    }

    public static MirCapabilities Capabilities(MirInstruction ir) => new(Support(ir), ir.Exit is not TrapExit,
        ir.Exit is TrapExit, ir.Operations.Any(op => OperationSpecs.For(op.Code).Effects.HasFlag(OperationEffects.MayStop)),
        ir.Operations.Any(op => op.Code == OpCode.Undefined), false, false, Obligations(ir));
}
