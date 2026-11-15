using System.Collections.Concurrent;
using System.Collections.Immutable;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.MethodCopies;

public sealed record MethodCopyCandidate(ulong RegisteredEntry, BindingEntry Entry);
public interface IMethodCopyCodeMap : IBindingCodeMap
{
    Reason? Failure(ulong entryOffset);
}

/// <summary>完成的身份事实按需缓存；同构的不同定义全部保留，调用点负责消歧。</summary>
public sealed class MethodCopyFacts : IMethodCopyCodeMap
{
    private readonly ConcurrentDictionary<ulong, ImmutableArray<MethodCopyCandidate>> entries;
    private readonly Func<ulong, ImmutableArray<MethodCopyCandidate>>? resolve;
    private readonly Func<ulong, Reason?>? failure;
    public MethodCopyFacts(IEnumerable<KeyValuePair<ulong, ImmutableArray<MethodCopyCandidate>>> entries,
        Func<ulong, ImmutableArray<MethodCopyCandidate>>? resolve = null, Func<ulong, Reason?>? failure = null)
    { this.entries = new(entries); this.resolve = resolve; this.failure = failure; }
    public ImmutableDictionary<ulong, ImmutableArray<MethodCopyCandidate>> Entries => entries.ToImmutableDictionary();
    public void Complete(ulong address, ImmutableArray<MethodCopyCandidate> candidates) => entries.TryAdd(address, candidates);
    public ImmutableArray<BindingEntry> At(ulong entryOffset)
    {
        var candidates = entries.TryGetValue(entryOffset, out var known) ? known : resolve?.Invoke(entryOffset) ?? [];
        return candidates.Select(c => c.Entry).Distinct().ToImmutableArray();
    }
    public Reason? Failure(ulong entryOffset) => failure?.Invoke(entryOffset);
    public static MethodCopyFacts Empty { get; } = new([]);
}
