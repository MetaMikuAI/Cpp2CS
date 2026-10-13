using System.Collections.Immutable;
using System.Numerics;
using System.Text.Json.Serialization;

namespace Cpp2CS.Ir;

public readonly record struct StateToken([property: JsonRequired] int Id);
public sealed record StateFlow(StateToken Input, StateToken Output);

[JsonPolymorphic(TypeDiscriminatorPropertyName = "$kind")]
[JsonDerivedType(typeof(NoPayload), "none")]
[JsonDerivedType(typeof(ImmediatePayload), "immediate")]
[JsonDerivedType(typeof(SlotPayload), "slot")]
[JsonDerivedType(typeof(ChoicePayload), "choice")]
[JsonDerivedType(typeof(GuardPayload), "guard")]
[JsonDerivedType(typeof(FloatPayload), "float")]
[JsonDerivedType(typeof(MemoryPayload), "memory")]
[JsonDerivedType(typeof(BarrierPayload), "barrier")]
[JsonDerivedType(typeof(AtomicPayload), "atomic")]
public abstract record OperationPayload
{
    private protected OperationPayload() { }
}

public sealed record NoPayload : OperationPayload
{
    public static readonly NoPayload Instance = new();
}
public sealed record ImmediatePayload(BigInteger Value) : OperationPayload;
public sealed record SlotPayload(string Name) : OperationPayload;
public sealed record ChoicePayload(string Reason) : OperationPayload;
public sealed record GuardPayload(StopKind Kind, string Reason) : OperationPayload;
public sealed record FloatPayload(FloatOperation Specification) : OperationPayload;
public sealed record MemoryPayload(MemoryOperation Specification) : OperationPayload;
public sealed record BarrierPayload(BarrierOperation Specification) : OperationPayload;
public sealed record AtomicPayload(AtomicOperation Specification) : OperationPayload;

public sealed record Operation(OpCode Code, Value? Result, ImmutableArray<Value> Inputs,
    OperationPayload Payload, StateFlow? Flow = null)
{
    [JsonIgnore] public BigInteger Immediate => Payload is ImmediatePayload p ? p.Value : default;
    [JsonIgnore] public string? Slot => (Payload as SlotPayload)?.Name;
    [JsonIgnore] public string? Detail => Payload switch { ChoicePayload p => p.Reason, GuardPayload p => p.Reason, _ => null };
    [JsonIgnore] public StopKind? StopKind => (Payload as GuardPayload)?.Kind;
    [JsonIgnore] public FloatOperation? Floating => (Payload as FloatPayload)?.Specification;
    [JsonIgnore] public MemoryOperation? Memory => (Payload as MemoryPayload)?.Specification;
    [JsonIgnore] public BarrierOperation? Barrier => (Payload as BarrierPayload)?.Specification;
    [JsonIgnore] public AtomicOperation? Atomic => (Payload as AtomicPayload)?.Specification;
}

[Flags]
public enum OperationEffects
{
    None = 0, ReadSlot = 1, WriteSlot = 2, Choice = 4,
    ReadMemory = 8, WriteMemory = 16, Environment = 32, Ordering = 64, MayStop = 128,
    ReadMonitor = 256, WriteMonitor = 512
}

public sealed record OperationSpec(int Arity, bool HasResult, Type PayloadType,
    OperationEffects Effects = OperationEffects.None, bool HasResidual = false)
{
    public bool HasStateFlow => Effects != OperationEffects.None;
}

public static class OperationSpecs
{
    private static readonly ImmutableDictionary<OpCode, OperationSpec> Table = Create();
    public static bool TryGet(OpCode code, out OperationSpec specification) => Table.TryGetValue(code, out specification!);
    public static OperationSpec For(OpCode code) => Table[code];
    public static OperationEffects EffectiveEffects(Operation op) => For(op.Code).Effects |
        (op.Memory is { Order: not MemoryOrder.Relaxed } ? OperationEffects.Ordering : OperationEffects.None);

    private static ImmutableDictionary<OpCode, OperationSpec> Create()
    {
        var entries = new Dictionary<OpCode, OperationSpec>();
        void Add(OpCode code, int arity, bool result, Type payload, OperationEffects effects = OperationEffects.None, bool residual = false) =>
            entries.Add(code, new(arity, result, payload, effects, residual));
        Add(OpCode.Constant, 0, true, typeof(ImmediatePayload));
        Add(OpCode.ReadSlot, 0, true, typeof(SlotPayload), OperationEffects.ReadSlot | OperationEffects.MayStop);
        Add(OpCode.WriteSlot, 1, false, typeof(SlotPayload), OperationEffects.WriteSlot);
        Add(OpCode.Extract, 1, true, typeof(ImmediatePayload));
        foreach (var code in new[] { OpCode.Zext, OpCode.Sext, OpCode.Not }) Add(code, 1, true, typeof(NoPayload));
        foreach (var code in new[] { OpCode.Concat, OpCode.Add, OpCode.Sub, OpCode.Mul, OpCode.And, OpCode.Or, OpCode.Xor,
                     OpCode.Shl, OpCode.Shr, OpCode.Sar, OpCode.Eq, OpCode.Ult, OpCode.Slt, OpCode.UDiv, OpCode.SDiv })
            Add(code, 2, true, typeof(NoPayload));
        Add(OpCode.Select, 3, true, typeof(NoPayload));
        Add(OpCode.Undefined, 0, true, typeof(ChoicePayload), OperationEffects.Choice);
        Add(OpCode.Float, 3, true, typeof(FloatPayload));
        Add(OpCode.FloatFused, 4, true, typeof(FloatPayload));
        Add(OpCode.Qarma5, 3, true, typeof(NoPayload));
        Add(OpCode.Guard, 1, false, typeof(GuardPayload), OperationEffects.MayStop, true);
        Add(OpCode.CodeGuarded, 1, true, typeof(NoPayload), OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.Load, 1, true, typeof(MemoryPayload), OperationEffects.ReadMemory | OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.Store, 2, false, typeof(MemoryPayload), OperationEffects.WriteMemory | OperationEffects.ReadMonitor | OperationEffects.WriteMonitor | OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.LoadIf, 2, true, typeof(NoPayload), OperationEffects.ReadMemory | OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.StoreIf, 3, false, typeof(NoPayload), OperationEffects.WriteMemory | OperationEffects.ReadMonitor | OperationEffects.WriteMonitor | OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.LoadExclusive, 1, true, typeof(MemoryPayload), OperationEffects.ReadMemory | OperationEffects.WriteMonitor | OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.StoreExclusive, 2, true, typeof(MemoryPayload), OperationEffects.WriteMemory | OperationEffects.ReadMonitor | OperationEffects.WriteMonitor | OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.ClearExclusive, 0, false, typeof(NoPayload), OperationEffects.WriteMonitor | OperationEffects.Environment | OperationEffects.Ordering, true);
        Add(OpCode.Barrier, 0, false, typeof(BarrierPayload), OperationEffects.Environment | OperationEffects.Ordering, true);
        Add(OpCode.Prefetch, 1, false, typeof(ImmediatePayload), OperationEffects.Environment | OperationEffects.Ordering, true);
        Add(OpCode.WriteProbe, 1, false, typeof(ImmediatePayload), OperationEffects.Environment | OperationEffects.MayStop, true);
        Add(OpCode.AtomicRmw, 3, true, typeof(AtomicPayload), OperationEffects.ReadMemory | OperationEffects.WriteMemory | OperationEffects.ReadMonitor | OperationEffects.WriteMonitor | OperationEffects.Environment | OperationEffects.Ordering | OperationEffects.MayStop, true);
        if (entries.Count != Enum.GetValues<OpCode>().Length) throw new InvalidOperationException("Every MIR opcode requires an operation specification");
        return entries.ToImmutableDictionary();
    }
}
