using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;

namespace Cpp2CS.Kernel.Flow;

public sealed record PrecedingBranch(BlockIdentity Branch, ImmutableArray<BlockIdentity> Between, BlockIdentity Successor);

/// <summary>沿唯一入边穿过无条件跳转，查询最近的前置分支；保留中间块，不判断其语义。</summary>
public sealed class PrecedingBranchQuery(StateQueries state) : Query<BlockIdentity, PrecedingBranch>
{
    public override Outcome<PrecedingBranch> Compute(QueryContext c, BlockIdentity key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<PrecedingBranch>();
        var current = key; var seen = new HashSet<BlockIdentity> { key }; var between = new List<BlockIdentity>();
        while (true)
        {
            if (c.Step() is { } why) return Outcome<PrecedingBranch>.Failure(why);
            if (!index.Value.Predecessors.TryGetValue(current, out var incoming) || incoming.Length != 1)
                return Outcome<PrecedingBranch>.Failure(new("flow.preceding-branch", "前置链没有唯一入边。"));
            var previous = incoming[0].Block;
            if (!seen.Add(previous)) return Outcome<PrecedingBranch>.Failure(new("flow.preceding-branch", "前置链含循环。"));
            var block = index.Value.Blocks[previous];
            if (block.End is Branch branch && (branch.True == current || branch.False == current))
                return Outcome<PrecedingBranch>.Success(new(previous, between.AsEnumerable().Reverse().ToImmutableArray(), current));
            if (block.End is not Jump jump || jump.Target != current || block.Statements.OfType<Call>().Any(call => call.Unwind == current))
                return Outcome<PrecedingBranch>.Failure(new("flow.preceding-branch", "前置链不是无条件跳转或正常分支边。"));
            between.Add(previous); current = previous;
        }
    }
}
