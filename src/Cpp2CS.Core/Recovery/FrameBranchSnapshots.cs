using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>不逃逸的帧片段按覆盖读取范围的到达写入回代；没有读取且无隐式栈实参的片段只删除其局部备份。</summary>
internal static class FrameBranchSnapshots
{
    internal static Dictionary<Stmt, Stmt> Read(MachineFunction function, Func<Call, long, int, bool> noStackRead)
    {
        var result = new Dictionary<Stmt, Stmt>(ReferenceEqualityComparer.Instance);
        if (function.Range.ExceptionRegions.Length != 0) return result;
        var sites = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i))).ToArray();
        var phiSources = sites.Select(s => s.Statement).OfType<Phi>().SelectMany(p => p.Sources).ToHashSet();
        var observed = sites.Select(s => s.Statement).Where(s => s is not Phi).SelectMany(ExprMap.Operands)
            .SelectMany(ExprMap.Walk).OfType<Use>().GroupBy(u => u.Variable)
            .ToDictionary(g => g.Key, g => g.Select(u => u.Width).Distinct().ToArray());
        // 只有本帧读取且所有用途恰好观察同一低位时，宽加载才可投影为标量；不猜未写入的高位。
        int ReadWidth(Stmt statement, Load load) => statement is Define d && d.Value == load && !phiSources.Contains(d.Target)
            && observed.GetValueOrDefault(d.Target) is [var scalar and (32 or 64)] && scalar < load.Width ? scalar : load.Width;
        var removed = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        var replacements = new Dictionary<Stmt, Dictionary<Load, Use>>(ReferenceEqualityComparer.Instance);
        foreach (var group in sites.Select(s => s.Statement).OfType<Store>()
            .Where(s => s is { Target: FrameAddress { Offset: < 0 }, Value: Use { Width: 64 or 128 } })
            .GroupBy(s => ((FrameAddress)s.Target).Offset))
        {
            var offset = group.Key;
            var width = group.Max(s => s.Value.Width);
            if (group.Count() < 2) continue;
            var end = offset + width / 8;
            var reads = new List<(Stmt Statement, Block Block, int Index, Load Load, int Width)>();
            bool Scan(Expr expression, Stmt statement, Block block, int index)
            {
                if (expression is Load { Address: FrameAddress frame } load)
                {
                    if (frame.Offset >= end || frame.Offset + load.Width / 8 <= offset) return true;
                    if (frame.Offset != offset || load.Width > width) return false;
                    reads.Add((statement, block, index, load, ReadWidth(statement, load)));
                    return true;
                }
                if (expression is FrameAddress address) return address.Offset >= end;
                return ExprMap.Children(expression).All(e => Scan(e, statement, block, index));
            }
            var safe = true;
            foreach (var (statement, block, index) in sites)
            {
                if (statement is Call call && !noStackRead(call, offset, width)) { safe = false; break; }
                if (statement is Store { Target: FrameAddress target } store)
                {
                    if (target.Offset < end && offset < target.Offset + store.Value.Width / 8
                        && (target.Offset != offset || store.Value is not Use || store.Value.Width is not (64 or 128))) { safe = false; break; }
                    safe = Scan(store.Value, statement, block, index);
                }
                else safe = ExprMap.Operands(statement).All(e => Scan(e, statement, block, index));
                if (!safe) break;
            }
            if (!safe) continue;
            Use? Reaching(Block block, int before, int readWidth, HashSet<Block> active)
            {
                if (!active.Add(block)) return null;
                foreach (var statement in block.Statements.Take(before).Reverse())
                    if (statement is Store { Target: FrameAddress target, Value: Use value } && target.Offset == offset)
                        return value.Width >= readWidth ? new Use(value.Variable, readWidth) : null;
                if (block.Predecessors.Count == 0) return null;
                var values = block.Predecessors.Select(p => Reaching(p, p.Statements.Count, readWidth, new(active))).Distinct().ToArray();
                return values is [Use same] ? same : null;
            }
            var bindings = reads.Select(r => (Read: r, Value: Reaching(r.Block, r.Index, r.Width, []))).ToArray();
            if (bindings.Any(b => b.Value is null)) continue;
            // 未被回代引用的源值还可能承担对象判空等可观察读取，只接受常量、入口值或本帧读取。
            bool UnusedSafe(Use value) => value.Variable.Version == 0 || sites.Select(s => s.Statement).OfType<Define>()
                .Where(d => d.Target == value.Variable).ToArray() is [var define] && (define.Value is Const
                    || define.Value is Load { Address: FrameAddress { Offset: < 0 } source } load && source.Offset + load.Width / 8 <= 0);
            if (group.Select(s => (Use)s.Value).Any(v => !bindings.Any(b => b.Value?.Variable == v.Variable) && !UnusedSafe(v))) continue;
            removed.UnionWith(group);
            foreach (var (read, value) in bindings)
            {
                if (!replacements.TryGetValue(read.Statement, out var map)) replacements[read.Statement] = map = [];
                map[read.Load] = value!;
            }
        }
        foreach (var (statement, _, _) in sites)
            if (removed.Contains(statement)) result[statement] = new Nop(statement.Address, "分支帧快照");
            else if (replacements.TryGetValue(statement, out var map))
                result[statement] = ExprMap.MapOperands(statement, e => ExprMap.Map(e, part => part is Load load && map.TryGetValue(load, out var value) ? value : null));
        return result;
    }
}
