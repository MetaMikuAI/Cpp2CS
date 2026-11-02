using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery.Control;

/// <summary>一个异常区域：Try 与 Handler 按块序排列，首块为入口；Catch 为取得托管异常的 catch（BeginCatch 所在），否则为 fault。</summary>
internal sealed record ExceptionRegionPlan(Block Pad, IReadOnlyList<Block> Try, IReadOnlyList<Block> Handler, Call? BeginCatch)
{
    public bool IsCatch => BeginCatch is not null;
}

/// <summary>
/// 由落地块构造 IL 异常区域。try：异常边指向落地块的块，取它们的最近公共支配者为入口，
/// 加上入口支配的、能到达这些块的全部块；所有从外部进入的边必须指向入口。处理块：落地块支配的块。
/// 落地块取得托管异常（BeginCatch）时为 catch（IL2CPP 对托管异常一律捕获 Il2CppExceptionWrapper，类型筛选在处理块的代码里），
/// 否则为只做清理的 fault。块序按区域嵌套排列，使每个区域在块序中连续。
/// </summary>
internal static class ExceptionRegions
{
    public static RecoveryResult<(IReadOnlyList<ExceptionRegionPlan> Regions, IReadOnlyList<Block> Order)> Build(MachineFunction function)
    {
        var pads = function.Blocks.Where(b => b.IsLandingPad && b.Predecessors.Any(p => p.Handler == b)).ToArray();
        var order = function.Blocks.ToList();
        if (pads.Length == 0) return (Array.Empty<ExceptionRegionPlan>(), order);
        var dominators = Dominators.Compute(function);
        var index = function.Blocks.Select((b, i) => (b, i)).ToDictionary(p => p.b, p => p.i);
        var regions = new List<ExceptionRegionPlan>();
        foreach (var pad in pads)
        {
            var throwing = function.Blocks.Where(b => b.Handler == pad).ToArray();
            var entry = throwing.Aggregate((a, b) => CommonDominator(dominators, function, a, b));
            var handler = function.Blocks.Where(b => dominators.Dominates(pad.Index, b.Index)).ToHashSet();
            var tryBlocks = Reaching(throwing, entry, dominators).Where(b => !handler.Contains(b)).ToHashSet();
            foreach (var block in tryBlocks)
                foreach (var predecessor in block.Predecessors)
                    if (block != entry && !tryBlocks.Contains(predecessor) && predecessor.Handler != block)
                        return RecoveryDiagnostics.Fail(block.Start, $"异常 try 区域有多个入口（0x{entry.Start:x}、0x{block.Start:x}）", rule: "Exceptions");
            foreach (var block in handler)
                foreach (var predecessor in block.Predecessors)
                    if (block != pad && !handler.Contains(predecessor))
                        return RecoveryDiagnostics.Fail(block.Start, "异常 处理块有落地块以外的入口", rule: "Exceptions");
            var beginCatch = pad.Statements.OfType<Call>().FirstOrDefault(c => c.Op?.Kind == OpKind.BeginCatch)
                ?? handler.SelectMany(b => b.Statements).OfType<Call>().FirstOrDefault(c => c.Op?.Kind == OpKind.BeginCatch);
            regions.Add(new(pad, tryBlocks.OrderBy(b => index[b]).ToArray(), handler.OrderBy(b => index[b]).ToArray(), beginCatch));
        }
        // 扩大 try 不得接管原本发往外层的异常。
        foreach (var region in regions)
            foreach (var block in region.Try)
                if (block.Handler is { } actual && actual != region.Pad && !region.Try.Contains(actual))
                    return RecoveryDiagnostics.Fail(block.Start, "异常 try 扩张覆盖了发往其他处理体的调用", rule: "Exceptions");
        // 区域之间只能嵌套（一个区域整体位于另一个的 try 或处理块中）或不相交。
        foreach (var a in regions)
            foreach (var b in regions)
            {
                if (ReferenceEquals(a, b)) continue;
                var all = a.Try.Concat(a.Handler).ToArray();
                if (!all.Any(x => b.Try.Contains(x) || b.Handler.Contains(x))) continue;
                if (all.All(b.Try.Contains) || all.All(b.Handler.Contains)) continue;
                var other = b.Try.Concat(b.Handler).ToArray();
                if (other.All(a.Try.Contains) || other.All(a.Handler.Contains)) continue;
                return RecoveryDiagnostics.Fail(a.Pad.Start, "异常 区域交叉", rule: "Exceptions");
            }
        return (regions, Layout(function.Blocks, regions));
    }

    private static Block CommonDominator(Dominators dominators, MachineFunction function, Block a, Block b)
    {
        var x = a.Index;
        var y = b.Index;
        while (!dominators.Dominates(x, y)) x = dominators.Idom[x];
        return function.Blocks[x];
    }

    /// <summary>入口支配的、能到达任一抛出块的块。</summary>
    private static IEnumerable<Block> Reaching(IReadOnlyCollection<Block> throwing, Block entry, Dominators dominators)
    {
        var result = new HashSet<Block>(throwing) { entry };
        var work = new Stack<Block>(throwing);
        while (work.Count > 0)
            foreach (var predecessor in work.Pop().Predecessors)
                if (dominators.Dominates(entry.Index, predecessor.Index) && result.Add(predecessor)) work.Push(predecessor);
        return result;
    }

    /// <summary>按区域嵌套排列块：区域的 try 与处理块各自连续，内层区域同样展开。</summary>
    private static IReadOnlyList<Block> Layout(IReadOnlyList<Block> scope, IReadOnlyList<ExceptionRegionPlan> regions)
    {
        var inScope = scope.ToHashSet();
        var candidates = regions.Where(r => r.Try.Concat(r.Handler).All(inScope.Contains)).ToArray();
        var top = candidates.Where(r => !candidates.Any(o => !ReferenceEquals(o, r)
            && r.Try.Concat(r.Handler).All(b => o.Try.Contains(b) || o.Handler.Contains(b))
            && o.Try.Count + o.Handler.Count > r.Try.Count + r.Handler.Count)).ToArray();
        var owner = new Dictionary<Block, ExceptionRegionPlan>();
        foreach (var region in top)
            foreach (var block in region.Try.Concat(region.Handler)) owner[block] = region;
        var result = new List<Block>();
        var done = new HashSet<ExceptionRegionPlan>();
        foreach (var block in scope)
        {
            if (!owner.TryGetValue(block, out var region)) { result.Add(block); continue; }
            if (!done.Add(region)) continue;
            var rest = regions.Where(r => !ReferenceEquals(r, region)).ToArray();
            result.AddRange(Layout(region.Try, rest));
            result.AddRange(Layout(region.Handler, rest));
        }
        return result;
    }
}
