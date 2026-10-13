namespace Cpp2CS.Ir;

public enum MemoryOrder { Relaxed, Acquire, Release }
public sealed record MemoryOperation(MemoryOrder Order, int ElementWidth, int AtomicWidth, bool NonTemporal = false);
public enum BarrierKind { Dmb, Dsb, Isb, Sfence, Lfence, Mfence }
public enum BarrierDomain { FullSystem, InnerShareable, OuterShareable, NonShareable }
public enum BarrierAccess { All, Loads, Stores }
public sealed record BarrierOperation(BarrierKind Kind, BarrierDomain Domain, BarrierAccess Access, int Option);
public sealed record ExclusiveReservation(ulong Address, int SizeBytes);
public sealed record ScheduledMemoryEvent(int BeforeEvent, ulong? Address, byte[] Bytes, bool InvalidateExclusive);
public sealed record WorldEvent(int Sequence, string Kind, ulong? Address, int SizeBytes, int AtomicWidth,
    MemoryOrder Order, string Outcome, int Option = 0, string? Data = null, BarrierOperation? Barrier = null,
    bool NonTemporal = false);
