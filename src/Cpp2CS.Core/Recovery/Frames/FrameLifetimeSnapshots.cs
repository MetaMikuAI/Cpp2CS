using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>栈备份在被覆盖前的全部读取回代为原 SSA 值，后续生命期可独立传址。</summary>
internal static class FrameLifetimeSnapshots
{
    internal static Dictionary<Stmt, Stmt> Read(MachineFunction function, Func<Call, long, int, bool> noStackRead,
        Func<Call, int, int?> argumentSize, Func<Expr, long?> frameOffset, IReadOnlySet<Stmt>? preserved = null)
    {
        var result = new Dictionary<Stmt, Stmt>(ReferenceEqualityComparer.Instance);
        if (function.Range.ExceptionRegions.Length != 0) return result;
        var sites = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i))).ToArray();
        var dominators = Dominators.Compute(function);
        var removed = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        var replacements = new Dictionary<Stmt, Dictionary<Load, Expr>>(ReferenceEqualityComparer.Instance);
        foreach (var site in sites)
        {
            if (preserved?.Contains(site.Statement) == true || site.Statement is not Store { Target: FrameAddress { Offset: < 0 } frame, Value: Use { Width: 32 or 64 or 128 } value } store)
                continue;
            var size = value.Width / 8;
            var end = frame.Offset + size;
            if (end > 0) continue;
            // 帧地址在普通表达式中外泄时，调用签名不足以界定它后续访问的范围。
            if (sites.Any(s => s.Statement is Define d && frameOffset(d.Value) is { } alias && alias < end
                || s.Statement is Store other && frameOffset(other.Value) is { } escaped && escaped < end)) continue;
            ulong Mask(long offset, long length)
            {
                var low = Math.Max(frame.Offset, offset);
                var high = Math.Min(end, offset + length);
                return low >= high ? 0 : ((1UL << (int)(high - low)) - 1) << (int)(low - frame.Offset);
            }
            var reads = new Dictionary<Stmt, Dictionary<Load, Expr>>(ReferenceEqualityComparer.Instance);
            var seen = new HashSet<(Block Block, int Index, ulong Live)>();
            bool Follow(Block block, int index, ulong live)
            {
                if (live == 0 || !seen.Add((block, index, live))) return true;
                if (seen.Count > 512) return false;
                for (var i = index; i < block.Statements.Count; i++)
                {
                    var statement = block.Statements[i];
                    bool Scan(Expr expression)
                    {
                        if (expression is Load load && frameOffset(load.Address) is { } from)
                        {
                            var touched = Mask(from, load.Width / 8);
                            if ((touched & live) == 0) return true;
                            if (preserved?.Contains(statement) == true || from < frame.Offset || from + load.Width / 8 > end || (touched & live) != touched
                                || (block == site.Block ? i <= site.Index : !dominators.Dominates(site.Block.Index, block.Index))) return false;
                            if (!reads.TryGetValue(statement, out var map)) reads[statement] = map = [];
                            map[load] = Fold.Extract(value, (int)(from - frame.Offset) * 8, load.Width);
                            return true;
                        }
                        if (frameOffset(expression) is { } address) return (Mask(address, Math.Max(0, end - address)) & live) == 0;
                        return ExprMap.Children(expression).All(Scan);
                    }
                    if (statement is Store write && frameOffset(write.Target) is { } to)
                    {
                        if (!Scan(write.Value)) return false;
                        live &= ~Mask(to, write.Value.Width / 8);
                        if (live == 0) return true;
                    }
                    else if (statement is Call call)
                    {
                        if (!noStackRead(call, frame.Offset, value.Width) || !Scan(call.Target)
                            || call.DelegateReceiver is { } receiver && !Scan(receiver)) return false;
                        for (var j = 0; j < call.Arguments.Length; j++)
                            if (frameOffset(call.Arguments[j]) is { } argument)
                            {
                                var length = argumentSize(call, j) ?? Math.Max(0, end - argument);
                                if ((Mask(argument, length) & live) != 0) return false;
                            }
                            else if (!Scan(call.Arguments[j])) return false;
                    }
                    else if (!ExprMap.Operands(statement).All(Scan)) return false;
                }
                return block.NormalSuccessors.All(next => Follow(next, 0, live));
            }
            if (!Follow(site.Block, site.Index + 1, (1UL << size) - 1) || reads.Count == 0) continue;
            removed.Add(store);
            foreach (var (statement, map) in reads)
            {
                if (!replacements.TryGetValue(statement, out var target)) replacements[statement] = target = [];
                foreach (var (load, replacement) in map) target[load] = replacement;
            }
        }
        foreach (var site in sites)
            if (removed.Contains(site.Statement)) result[site.Statement] = new Nop(site.Statement.Address, "帧生命期快照");
            else if (replacements.TryGetValue(site.Statement, out var map))
                result[site.Statement] = ExprMap.MapOperands(site.Statement, e => ExprMap.Map(e,
                    part => part is Load load && map.TryGetValue(load, out var value) ? value : null));
        return result;
    }
}
