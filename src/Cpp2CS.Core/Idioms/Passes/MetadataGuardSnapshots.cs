using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Idioms;

/// <summary>元数据初始化不修改对象字段；守卫两侧的字段快照按合流后的读取位宽核对。</summary>
internal static class MetadataGuardSnapshots
{
    internal static bool Equivalent(MachineFunction function, Block head, IReadOnlyList<Block> slow, IReadOnlyList<Block> fast, Block merge)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var phis = function.Blocks.SelectMany(b => b.Statements).OfType<Phi>().ToArray();
        var uses = function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk)
            .OfType<Use>().ToLookup(u => u.Variable);
        int Observed(Variable variable, HashSet<Variable> seen)
        {
            if (!seen.Add(variable)) return 0;
            return Math.Max(uses[variable].Select(u => u.Width).DefaultIfEmpty(0).Max(),
                phis.Where(p => p.Sources.Contains(variable)).Select(p => Observed(p.Target, seen)).DefaultIfEmpty(0).Max());
        }
        Expr Expand(Expr value, int depth = 0) => depth >= 32 ? value : Fold.Simplify(ExprMap.Map(value, e =>
            e is Use use && definitions.TryGetValue(use.Variable, out var source)
                ? Fold.Convert(ConvKind.Truncate, Expand(source, depth + 1), use.Width) : null));
        Expr? Snapshot(Load load)
        {
            var address = Expand(load.Address);
            var (root, offset) = SplitPass.Split(address);
            // 元数据槽位与栈位置不属于此处的对象字段证明。
            if (root is Const or Symbol or FrameAddress || offset < RuntimeLayout.ObjectHeaderSize) return null;
            var visited = new HashSet<Block>();
            var block = head;
            while (visited.Add(block))
            {
                foreach (var statement in block.Statements.AsEnumerable().Reverse())
                {
                    if (statement is Define define)
                    {
                        var source = define.Value;
                        while (source is Ir.Convert { Kind: ConvKind.ZeroExtend } conversion) source = conversion.Operand;
                        if (source is Load read && Expand(read.Address) == address && read.Width == load.Width)
                            return new Use(define.Target, load.Width);
                    }
                    if (statement is Store store)
                    {
                        var (written, at) = SplitPass.Split(Expand(store.Target));
                        if (written == root && offset >= at && offset - at + (ulong)load.Width / 8 <= (ulong)store.Value.Width / 8)
                            return Fold.Extract(store.Value, checked((int)(offset - at) * 8), load.Width);
                        return null;
                    }
                    if (statement is not (Define or Phi or Nop or Jump or Branch)) return null;
                }
                if (block.IsLandingPad || block.Predecessors is not [var previous]) return null;
                block = previous;
            }
            return null;
        }
        foreach (var define in slow.SelectMany(b => b.Statements).OfType<Define>())
        {
            var loads = ExprMap.Walk(define.Value).OfType<Load>().Distinct().ToArray();
            var snapshots = loads.Select(Snapshot).ToArray();
            if (snapshots.Any(s => s is null)) return false;
            definitions[define.Target] = ExprMap.Map(define.Value, e => e is Load load
                ? snapshots[Array.IndexOf(loads, load)] : null);
        }
        var skipped = merge.Predecessors.IndexOf(fast[^1]);
        var initialized = merge.Predecessors.IndexOf(slow[^1]);
        return skipped >= 0 && initialized >= 0 && merge.Statements.OfType<Phi>().All(phi =>
            phi.Sources.Length == merge.Predecessors.Count && (Observed(phi.Target, []) is var width && (width == 0
                || Expand(new Use(phi.Sources[skipped], width)) == Expand(new Use(phi.Sources[initialized], width)))));
    }
}
