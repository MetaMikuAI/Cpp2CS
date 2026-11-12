using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Locations;

internal readonly record struct ManagedReadSnapshot(ReadIdentity Read, Term Source);

/// <summary>投影读取的原定义必须支配来源项的全部使用；复用程序点支配查询。</summary>
internal sealed class ManagedReadSnapshotQuery(StateQueries state) : Query<ManagedReadSnapshot, bool>
{
    private readonly FlowQueries flow = new();
    public override Outcome<bool> Compute(QueryContext c, ManagedReadSnapshot key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<bool>();
        var read = index.Value.Reads[key.Read];
        foreach (var block in c.Snapshot.Blocks)
            for (int i = 0; i <= block.Statements.Length; i++)
            {
                var uses = i == block.Statements.Length ? SnapshotRewrite.Uses(block.End) : SnapshotRewrite.Uses(block.Statements[i]);
                foreach (var use in uses)
                {
                    var resolved = c.Get(state.Resolve, use); if (!resolved.IsSuccess) return resolved.Propagate<bool>();
                    if (!SnapshotRewrite.Dependencies([resolved.Value]).Contains(key.Source)) continue;
                    var dominates = c.Get(flow.PointDominates, new(read.Point, new(block.Identity, i)));
                    if (!dominates.IsSuccess || !dominates.Value) return dominates;
                }
            }
        return Outcome<bool>.Success(true);
    }
}
