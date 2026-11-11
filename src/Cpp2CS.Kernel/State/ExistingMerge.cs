using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.State;

public readonly record struct ExistingMergeKey(BlockIdentity Block, ImmutableArray<Incoming> Inputs);
/// <summary>按入边对应值查找快照中已有的合流，不制造新的值定义。</summary>
public sealed class ExistingMergeQuery(StateQueries state) : Query<ExistingMergeKey, Term>
{
    public override Outcome<Term> Compute(QueryContext c, ExistingMergeKey key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<Term>();
        foreach (var merge in index.Value.Blocks[key.Block].Merges)
        {
            if (merge.Inputs.Length != key.Inputs.Length) continue;
            bool matches = true;
            foreach (var input in merge.Inputs)
            {
                var wanted = key.Inputs.Where(i => i.Predecessor == input.Predecessor).ToArray();
                if (wanted.Length != 1) { matches = false; break; }
                var left = c.Get(state.Resolve, input.Value); if (!left.IsSuccess) return left;
                var right = c.Get(state.Resolve, wanted[0].Value); if (!right.IsSuccess) return right;
                if (left.Value != right.Value) { matches = false; break; }
            }
            if (matches) return Outcome<Term>.Success(merge.Result);
        }
        return Outcome<Term>.Failure(new("state.existing-merge", "没有逐入边对应的已有合流值。"));
    }
}
