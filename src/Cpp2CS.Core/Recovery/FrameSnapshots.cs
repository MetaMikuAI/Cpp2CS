using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>单次写入且地址不逃逸的帧片段可读取原 SSA 快照，不移动原始访存。</summary>
internal static class FrameSnapshots
{
    internal static Dictionary<Stmt, Stmt> Read(MachineFunction function)
    {
        var sites = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i))).ToArray();
        var candidates = sites.Where(p => p.Statement is Store { Target: FrameAddress { Offset: < 0 }, Value: Use { Width: 64 or 128 } }).ToArray();
        if (candidates.Length == 0) return new(ReferenceEqualityComparer.Instance);
        var dominators = Dominators.Compute(function);
        var substitutions = new Dictionary<long, Use>();
        var removed = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        foreach (var site in candidates)
        {
            if (site.Statement is not Store { Target: FrameAddress { Offset: < 0 } frame, Value: Use { Width: 64 or 128 } value } store) continue;
            var bytes = value.Width / 8;
            bool Overlaps(long at, int size) => at < frame.Offset + bytes && frame.Offset < at + size;
            var reads = 0;
            bool Safe(Expr expression)
            {
                if (expression is Load { Address: FrameAddress from } load)
                {
                    if (!Overlaps(from.Offset, load.Width / 8)) return true;
                    if (from.Offset != frame.Offset || load.Width != value.Width) return false;
                    reads++;
                    return true;
                }
                if (expression is FrameAddress address) return address.Offset >= frame.Offset + bytes;
                return ExprMap.Children(expression).All(Safe);
            }
            var valid = true;
            foreach (var use in sites)
            {
                if (ReferenceEquals(use.Statement, store)) continue;
                var before = reads;
                if (use.Statement is Store { Target: FrameAddress target } other)
                {
                    if (Overlaps(target.Offset, other.Value.Width / 8) || !Safe(other.Value)) { valid = false; break; }
                }
                else if (!ExprMap.Operands(use.Statement).All(Safe)) { valid = false; break; }
                if (reads != before && (use.Block == site.Block ? use.Index <= site.Index : !dominators.Dominates(site.Block.Index, use.Block.Index)))
                { valid = false; break; }
            }
            if (!valid || reads == 0) continue;
            substitutions.Add(frame.Offset, value);
            removed.Add(store);
        }
        var result = new Dictionary<Stmt, Stmt>(ReferenceEqualityComparer.Instance);
        foreach (var site in sites)
        {
            var mapped = removed.Contains(site.Statement) ? new Nop(site.Statement.Address, "帧快照")
                : ExprMap.MapOperands(site.Statement, e => ExprMap.Map(e, part => part is Load { Address: FrameAddress from } load
                    && substitutions.TryGetValue(from.Offset, out var value) && value.Width == load.Width ? value : null));
            if (!ReferenceEquals(mapped, site.Statement)) result.Add(site.Statement, mapped);
        }
        return result;
    }
}
