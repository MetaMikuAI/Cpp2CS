using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>提交帧内存分析证明的快照替换，不移动原始访存。</summary>
internal static class FrameSnapshots
{
    internal static Dictionary<Stmt, Stmt> Read(MachineFunction function, Action<RuleTrace>? trace = null, Func<Expr, long?>? frameOffset = null)
    {
        var memory = new FrameMemory(function, frameOffset);
        var bindings = new List<FrameSnapshotValue>();
        var candidates = new List<(StatementSite Site, RewriteResult<FrameSnapshotValue> Result)>();
        foreach (var site in memory.Sites)
        {
            var candidate = memory.Snapshot(site);
            if (candidate.Status != RewriteStatus.NoMatch) candidates.Add((site, candidate));
            if (candidate.Status == RewriteStatus.Applied) bindings.Add(candidate.Value!);
        }
        // 重叠读取须全部有快照替换；任一片因逃逸或旁路被拒绝时，依赖它的片也保留原访存。
        bool Covered(FrameSnapshotValue binding) => binding.Reads.SelectMany(r => ExprMap.Operands(r.Statement))
            .SelectMany(ExprMap.Walk).OfType<Load>().All(load => load.Address is not FrameAddress frame
                || !binding.Version.Storage.Range.Overlaps(new(frame.Offset, load.Width / 8))
                || bindings.Any(b => b.Version.Storage.Range.Offset == frame.Offset && b.Value.Width == load.Width));
        while (true)
        {
            var rejected = bindings.Where(b => !Covered(b)).ToHashSet();
            if (rejected.Count == 0) break;
            bindings.RemoveAll(rejected.Contains);
        }
        foreach (var (site, candidate) in candidates)
        {
            var decision = candidate.Status == RewriteStatus.Applied && !bindings.Contains(candidate.Value!)
                ? RewriteResult<FrameSnapshotValue>.Blocked("storage.snapshot-dependency", "重叠读取的其他快照未通过证明") : candidate;
            trace?.Invoke(new("storage.single-write-snapshot", site.Statement.Address, decision.Status, decision.Code, decision.Detail, decision.Evidence));
        }
        var substitutions = bindings.ToDictionary(b => b.Version.Storage.Range.Offset, b => b.Value);
        var removed = bindings.Select(b => b.Store).ToHashSet<Stmt>(ReferenceEqualityComparer.Instance);
        var result = new Dictionary<Stmt, Stmt>(ReferenceEqualityComparer.Instance);
        foreach (var site in memory.Sites)
        {
            var mapped = removed.Contains(site.Statement) ? new Nop(site.Statement.Address, "帧快照")
                : ExprMap.MapOperands(site.Statement, e => ExprMap.Map(e, part => part is Load { Address: FrameAddress from } load
                    && substitutions.TryGetValue(from.Offset, out var value) && value.Width == load.Width ? value : null));
            if (!ReferenceEquals(mapped, site.Statement)) result.Add(site.Statement, mapped);
        }
        return result;
    }
}
