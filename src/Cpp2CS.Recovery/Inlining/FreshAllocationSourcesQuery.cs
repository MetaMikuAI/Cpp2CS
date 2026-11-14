using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

internal sealed record FreshAllocationSources(ImmutableArray<AllocationConstructorRequest> Inputs, ImmutableHashSet<Term> Aliases);

/// <summary>只展开引用合流的值图；每个有限叶来源必须是已绑定的新分配。</summary>
internal sealed class FreshAllocationSourcesQuery(StateQueries state, IReadOnlyDictionary<Term, AllocationConstructorRequest> allocations)
    : Query<Term, FreshAllocationSources>
{
    private sealed class MergeIndex : Query<int, ImmutableDictionary<Term, Merge>>
    {
        public override Outcome<ImmutableDictionary<Term, Merge>> Compute(QueryContext c, int key) =>
            Outcome<ImmutableDictionary<Term, Merge>>.Success(c.Snapshot.Blocks.SelectMany(b => b.Merges).ToImmutableDictionary(m => m.Result));
    }
    private readonly MergeIndex index = new();
    public override Outcome<FreshAllocationSources> Compute(QueryContext c, Term key)
    {
        var indexed = c.Get(index, 0); if (!indexed.IsSuccess) return indexed.Propagate<FreshAllocationSources>();
        var inputs = new Dictionary<Term, AllocationConstructorRequest>(); var aliases = new HashSet<Term>(); var active = new HashSet<Term>();
        Outcome<bool> No(string message, Reason? cause = null) => Outcome<bool>.Failure(new("inline.Allocation.Sources", message, cause));
        Outcome<bool> Read(Term term)
        {
            if (c.Step() is { } budget) return No("分配来源证明预算耗尽。", budget);
            var value = c.Get(state.Resolve, term); if (!value.IsSuccess) return value.Propagate<bool>();
            if (value.Value.Width != c.Snapshot.AddressWidth || value.Value.ContainsUndefined) return No("输入不是完整、有定义的引用。");
            if (active.Contains(value.Value)) return No("分配来源的合流值图含循环。");
            if (!aliases.Add(value.Value)) return Outcome<bool>.Success(true);
            if (allocations.TryGetValue(value.Value, out var allocation))
            { inputs.TryAdd(allocation.Result, allocation); return Outcome<bool>.Success(true); }
            if (!indexed.Value.TryGetValue(value.Value, out var merge) || merge.Inputs.IsEmpty) return No("输入不是已证明的新分配或引用合流。");
            active.Add(value.Value);
            for (int i = 0; i < merge.Inputs.Length; i++)
            {
                var input = Read(merge.Inputs[i].Value);
                if (!input.IsSuccess) return No($"对象合流第 {i} 个输入不是已证明的新分配。", input.Why);
            }
            active.Remove(value.Value); return Outcome<bool>.Success(true);
        }
        var result = Read(key);
        return result.IsSuccess && inputs.Count != 0 ? Outcome<FreshAllocationSources>.Success(new(inputs.Values.ToImmutableArray(), aliases.ToImmutableHashSet()))
            : Outcome<FreshAllocationSources>.Failure(result.Why ?? new("inline.Allocation.Sources", "对象合流没有新分配来源。"));
    }
}
