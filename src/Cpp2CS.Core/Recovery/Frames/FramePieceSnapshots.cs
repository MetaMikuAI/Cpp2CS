using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>连续且不逃逸的栈备份允许跨片读取；所有读取均须受完整写入支配，按原 SSA 快照拼接。</summary>
internal static class FramePieceSnapshots
{
    internal static Dictionary<Stmt, Stmt> Read(MachineFunction function, Func<Call, long, int, bool> noStackRead,
        Func<Expr, long?> frameOffset)
    {
        var result = new Dictionary<Stmt, Stmt>(ReferenceEqualityComparer.Instance);
        if (function.Range.ExceptionRegions.Length != 0) return result;
        var sites = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i))).ToArray();
        var removed = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        var replacements = new Dictionary<Stmt, Dictionary<Load, Expr>>(ReferenceEqualityComparer.Instance);
        Dominators? dominators = null;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var stores = new List<Store>();
                while (i < block.Statements.Count && block.Statements[i] is Store
                    { Target: FrameAddress { Offset: < 0 } frame, Value: Use { Width: 32 or 64 or 128 } value } store
                    && frame.Offset + value.Width / 8 <= 0)
                { stores.Add(store); i++; }
                if (stores.Count < 2) continue;
                var lastIndex = i - 1;
                var ordered = stores.OrderBy(s => ((FrameAddress)s.Target).Offset).ToArray();
                var start = ((FrameAddress)ordered[0].Target).Offset;
                var end = start;
                var contiguous = true;
                foreach (var store in ordered)
                {
                    contiguous &= ((FrameAddress)store.Target).Offset == end;
                    end += store.Value.Width / 8;
                }
                if (!contiguous || end - start > 64) continue;
                var reads = new List<(Stmt Statement, Load Load)>();
                bool Scan(Expr expression, Stmt statement)
                {
                    if (expression is Load load && frameOffset(load.Address) is { } from)
                    {
                        if (from >= end || from + load.Width / 8 <= start) return true;
                        if (load.Address is not FrameAddress || from < start || from + load.Width / 8 > end
                            || load.Width is not (32 or 64 or 128)) return false;
                        reads.Add((statement, load));
                        return true;
                    }
                    if (frameOffset(expression) is { } escaped) return escaped >= end;
                    return ExprMap.Children(expression).All(e => Scan(e, statement));
                }
                var safe = true;
                foreach (var site in sites)
                {
                    if (stores.Any(s => ReferenceEquals(s, site.Statement))) continue;
                    var count = reads.Count;
                    if (site.Statement is Call call && !noStackRead(call, start, checked((int)(end - start) * 8))) { safe = false; break; }
                    if (site.Statement is Store other && frameOffset(other.Target) is { } to)
                        safe = (to >= end || to + other.Value.Width / 8 <= start) && Scan(other.Value, other);
                    else safe = ExprMap.Operands(site.Statement).All(e => Scan(e, site.Statement));
                    if (!safe) break;
                    if (count == reads.Count) continue;
                    dominators ??= Dominators.Compute(function);
                    if (site.Block == block ? site.Index <= lastIndex : !dominators.Dominates(block.Index, site.Block.Index))
                    { safe = false; break; }
                }
                if (!safe || !reads.Any(r => !stores.Any(s => s.Target == r.Load.Address && s.Value.Width == r.Load.Width))) continue;
                removed.UnionWith(stores);
                foreach (var (statement, load) in reads)
                {
                    var from = ((FrameAddress)load.Address).Offset;
                    Expr composed = Expr.C(0, load.Width);
                    foreach (var store in ordered)
                    {
                        var source = ((FrameAddress)store.Target).Offset;
                        var low = Math.Max(source, from);
                        var high = Math.Min(source + store.Value.Width / 8, from + load.Width / 8);
                        for (var at = low; at < high;)
                        {
                            var bytes = Math.Min(8, high - at);
                            if (bytes is not (1 or 2 or 4 or 8)) bytes = 1;
                            var piece = Fold.Extract(store.Value, checked((int)(at - source) * 8), checked((int)bytes * 8));
                            composed = new Insert(composed, piece, checked((int)(at - from) * 8));
                            at += bytes;
                        }
                    }
                    if (!replacements.TryGetValue(statement, out var map)) replacements[statement] = map = [];
                    map[load] = composed;
                }
            }
        foreach (var site in sites)
            if (removed.Contains(site.Statement)) result[site.Statement] = new Nop(site.Statement.Address, "分片帧快照");
            else if (replacements.TryGetValue(site.Statement, out var map))
                result[site.Statement] = ExprMap.MapOperands(site.Statement, e => ExprMap.Map(e,
                    part => part is Load load && map.TryGetValue(load, out var value) ? value : null));
        return result;
    }
}
