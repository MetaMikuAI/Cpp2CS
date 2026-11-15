using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Structure;

/// <summary>按快照索引直接使用与合流传递；不同区域的边界视图共用索引。</summary>
internal sealed class StructureLiveness
{
    private readonly Dictionary<Term, HashSet<(BlockIdentity Block, bool End)>> users;
    private readonly Dictionary<Term, HashSet<Term>> consumers;
    private readonly IReadOnlySet<Term>? boundaries;
    private readonly Dictionary<Term, HashSet<(BlockIdentity Block, bool End)>> appended = [];

    public StructureLiveness(NativeFunction function, Func<Terminator, IEnumerable<Term>> endUses,
        IReadOnlySet<Term>? boundaries = null, BlockIdentity? appendedAt = null, IEnumerable<Term>? appendedUses = null,
        Func<Statement, IEnumerable<Term>>? statementUses = null)
    {
        users = []; consumers = []; this.boundaries = boundaries;
        foreach (var block in function.Blocks)
        {
            Add(users, block.Statements.SelectMany(statementUses ?? SnapshotRewrite.Uses), (block.Identity, false));
            Add(users, endUses(block.End), (block.Identity, true));
            foreach (var merge in block.Merges)
                foreach (var input in SnapshotRewrite.Dependencies(merge.Inputs.Select(i => i.Value)))
                {
                    if (!consumers.TryGetValue(input, out var targets)) consumers[input] = targets = [];
                    targets.Add(merge.Result);
                }
        }
        if (appendedAt is not null && appendedUses is not null) Add(appended, appendedUses, (appendedAt, false));
    }

    public StructureLiveness(StructureLiveness index, IReadOnlySet<Term> boundaries,
        BlockIdentity? appendedAt = null, IEnumerable<Term>? appendedUses = null)
    {
        users = index.users; consumers = index.consumers;
        this.boundaries = index.boundaries is null ? boundaries : index.boundaries.Concat(boundaries).ToHashSet();
        foreach (var (value, points) in index.appended) appended[value] = [.. points];
        if (appendedAt is not null && appendedUses is not null) Add(appended, appendedUses, (appendedAt, false));
    }

    private static void Add(Dictionary<Term, HashSet<(BlockIdentity Block, bool End)>> index,
        IEnumerable<Term> roots, (BlockIdentity Block, bool End) point)
    {
        foreach (var value in SnapshotRewrite.Dependencies(roots))
        {
            if (!index.TryGetValue(value, out var points)) index[value] = points = [];
            points.Add(point);
        }
    }

    private (bool Used, bool Matches) Uses(Term value, Func<(BlockIdentity Block, bool End), bool> predicate)
    {
        var seen = new HashSet<Term>(); var pending = new Stack<Term>(); pending.Push(value);
        bool used = false;
        while (pending.TryPop(out var current))
        {
            if (!seen.Add(current)) continue;
            foreach (var index in new[] { users, appended })
                if (index.TryGetValue(current, out var points))
                {
                    used |= points.Count != 0;
                    if (points.Any(predicate)) return (true, true);
                }
            if (consumers.TryGetValue(current, out var targets))
                foreach (var target in targets)
                    if (boundaries?.Contains(target) != true) pending.Push(target);
        }
        return (used, false);
    }

    public bool OnlyAt(Term value, IReadOnlySet<(BlockIdentity Block, bool End)> allowed)
    {
        var result = Uses(value, point => !allowed.Contains(point));
        return result.Used && !result.Matches;
    }
    public bool Inside(Term value, IReadOnlySet<BlockIdentity> members) => Uses(value, point => members.Contains(point.Block)).Matches;
    public bool Used(Term value) => Uses(value, _ => true).Matches;
    public bool Outside(Term value, HashSet<BlockIdentity> inside, BlockIdentity head) =>
        Uses(value, point => !inside.Contains(point.Block) && !(point.End && point.Block == head)).Matches;
}
