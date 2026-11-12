using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;

namespace Cpp2CS.Recovery.Inlining;

public sealed record AccessorReadPlacement(ReadIdentity Definition, IReadOnlyList<ReadIdentity> Occurrences);

/// <summary>读取共用局部时，原定义必须支配其余读取；只用现有程序点支配查询。</summary>
public sealed class AccessorReadPlacementQuery : Query<AccessorReadPlacement, bool>
{
    private readonly FlowQueries flow = new();
    public override Outcome<bool> Compute(QueryContext c, AccessorReadPlacement key)
    {
        var reads = c.Snapshot.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Point: new Point(b.Identity, i))))
            .Where(p => p.Statement is MemoryRead).ToDictionary(p => ((MemoryRead)p.Statement).Identity, p => p.Point);
        if (!reads.TryGetValue(key.Definition, out var definition)) return Outcome<bool>.Success(false);
        foreach (var occurrence in key.Occurrences)
        {
            if (occurrence == key.Definition) continue;
            if (!reads.TryGetValue(occurrence, out var point)) return Outcome<bool>.Success(false);
            var dominates = c.Get(flow.PointDominates, new(definition, point));
            if (!dominates.IsSuccess || !dominates.Value) return dominates.IsSuccess ? Outcome<bool>.Success(false) : dominates;
        }
        return Outcome<bool>.Success(true);
    }
}
