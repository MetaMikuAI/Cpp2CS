using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Memory;

namespace Cpp2CS.Recovery;

/// <summary>提交帧内存分析证明的快照替换，不移动原始访存。</summary>
internal static class FrameSnapshots
{
    internal static Dictionary<Stmt, Stmt> Read(MachineFunction function, Action<RuleTrace>? trace = null)
    {
        var memory = new FrameMemory(function);
        var bindings = new List<FrameSnapshotValue>();
        foreach (var site in memory.Sites)
        {
            var candidate = memory.Snapshot(site);
            if (candidate.Status != RewriteStatus.NoMatch)
                trace?.Invoke(new("storage.single-write-snapshot", site.Statement.Address, candidate.Status, candidate.Code, candidate.Detail, candidate.Evidence));
            if (candidate.Status == RewriteStatus.Applied) bindings.Add(candidate.Value!);
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
