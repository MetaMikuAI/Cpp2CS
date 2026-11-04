namespace Cpp2CS.Recovery.Effects;

[Flags]
public enum EffectKind { None = 0, Read = 1, Write = 2, Capture = 4, Allocate = 8, Initialize = 16, Order = 32 }

[Flags]
public enum ExceptionEffect { None = 0, NullReference = 1, Bounds = 2, Other = 4, Any = NullReference | Bounds | Other }

public enum MemoryKind { Local, Instance, Static, Element, Reference, Metadata, Unknown }

/// <summary>可观察效果的保守上界；未知操作不能当作纯操作。读取、抛出与写入分别记录。</summary>
public readonly record struct EffectSummary(EffectKind Kinds, ExceptionEffect Exceptions = ExceptionEffect.None)
{
    public static EffectSummary None => default;
    public static EffectSummary Unknown => new(EffectKind.Read | EffectKind.Write | EffectKind.Capture
        | EffectKind.Allocate | EffectKind.Initialize | EffectKind.Order, ExceptionEffect.Any);
    public bool MayThrow => Exceptions != ExceptionEffect.None;
    public bool InvalidatesMemory => (Kinds & (EffectKind.Write | EffectKind.Capture | EffectKind.Initialize | EffectKind.Order)) != 0;
    public bool CanDiscard => !MayThrow && (Kinds & ~EffectKind.Read) == 0;
    public bool CanDuplicate => CanDiscard && (Kinds & EffectKind.Read) == 0;
    public static EffectSummary operator |(EffectSummary a, EffectSummary b) => new(a.Kinds | b.Kinds, a.Exceptions | b.Exceptions);

    public static EffectSummary Access(MemoryKind kind, bool write = false, bool nonNull = false) => new(
        (write ? EffectKind.Write : EffectKind.Read) | (kind == MemoryKind.Static ? EffectKind.Initialize : EffectKind.None),
        kind switch
        {
            MemoryKind.Local or MemoryKind.Metadata => ExceptionEffect.None,
            MemoryKind.Instance => nonNull ? ExceptionEffect.None : ExceptionEffect.NullReference,
            MemoryKind.Element => ExceptionEffect.Bounds | (nonNull ? ExceptionEffect.None : ExceptionEffect.NullReference),
            _ => ExceptionEffect.Any,
        });
}
