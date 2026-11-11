using System.Collections.Immutable;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Terms;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Binding;

public enum BindingFailureKind { SignatureUnavailable, ClassificationFailed, EntryNotMapped, AmbiguousCandidates, MissingSlot }
public sealed record BindingFailure(BindingFailureKind Kind, string Detail);
public sealed record BindingResult<T>(T? Value, BindingFailure? Failure) where T : class
{
    public bool Success => Value is not null && Failure is null;
    public static BindingResult<T> Fail(BindingFailureKind kind, string detail) => new(null, new(kind, detail));
}

/// <summary>代码地图由装配方投影；泛型表没有非共享见证时用 SharedGeneric，不按实例类型猜测。</summary>
public enum BindingEntryKind { Ordinary, SharedGeneric, AdjustorThunk, Invoker, Wrapper }
public sealed record BindingEntry(MethodRef? Method, BindingEntryKind Kind, string? Detail = null);
public interface IBindingCodeMap
{
    /// <summary>地址与 ImageFunction 一致，均为相对映像基址的偏移；保留全部候选。</summary>
    ImmutableArray<BindingEntry> At(ulong entryOffset);
}

public sealed record SignatureBinding(CSignature Signature, SlotAssignment Slots,
    ManagedCSignature? Managed = null, BindingEntry? Entry = null)
{
    public AbiValue? This => Managed?.ThisIndex is { } i ? Slots.Parameters[i] : null;
    public ImmutableArray<AbiValue> Parameters => Managed is { } m
        ? m.ParameterIndices.Select(i => Slots.Parameters[i]).ToImmutableArray() : Slots.Parameters;
    public AbiValue? MethodInformation => Managed is { } m ? Slots.Parameters[m.MethodInformationIndex] : null;
}

/// <summary>所有偏移与长度以字节计；栈片段的地址是实参区基址，Offset 已含槽内偏移。</summary>
public abstract record BoundSource;
public sealed record TermSource(Term Term) : BoundSource;
public sealed record StackSource(Term Area, long Offset, int Length) : BoundSource;
public sealed record BoundPiece(int ValueOffset, int Length, BoundSource Source);
/// <summary>含待读取的栈片段；未列出的字节只是聚合填充，不是零。</summary>
public sealed record PiecesSource(ImmutableArray<BoundPiece> Pieces) : BoundSource;
/// <summary>Address 的值是副本/结果缓冲区指针；若地址在栈上，先由状态模型读指针。</summary>
public sealed record IndirectSource(BoundSource Address, int Length) : BoundSource;
public sealed record BoundValue(CType Type, BoundSource? Source, UnusedBitRule UnusedBits);
public sealed record BoundCall(SignatureBinding Signature, ImmutableArray<BoundValue> Arguments, BoundValue Result)
{
    public BoundValue? This => Signature.Managed?.ThisIndex is { } i ? Arguments[i] : null;
    public ImmutableArray<BoundValue> Parameters => Signature.Managed is { } m
        ? m.ParameterIndices.Select(i => Arguments[i]).ToImmutableArray() : Arguments;
    public BoundValue? MethodInformation => Signature.Managed is { } m ? Arguments[m.MethodInformationIndex] : null;
}
public sealed record CandidateBinding(BindingEntry Entry, BindingResult<BoundCall> Binding);
/// <summary>多候选时 Failure 标明歧义，Candidates 仍保留每个候选的绑定或具体失败。</summary>
public sealed record CallCandidates(ImmutableArray<CandidateBinding> Candidates, BindingFailure? Failure);
