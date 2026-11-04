using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Effects;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>
/// 机械下降：按块把机器语句的效果写成托管语句。值从符号值按期望类型得到视图——数据搬运不产生语句，
/// 运算成为 IL 运算，读取按位置成为字段、元素或长度；读取只在被所在语句之外使用时落成局部；
/// 调用按机器签名重组 IL 实参，经指针的 ref 实参与结果缓冲区成为局部；φ 成为局部并在入边上并行赋值，
/// 不冲突的复制两端由 <see cref="LocalCoalescing"/> 合成同一个局部。
/// 表达不了的值与语句记为洞，方法体作为部分体保留。
/// </summary>
internal sealed partial class BodyBuilder
{
    private readonly MethodAnalysis analysis;
    private readonly TypeOracle oracle;
    private readonly ManagedTypes types;
    private readonly ValueModel values;
    private readonly Dictionary<Sym, LocalValue> locals = [];
    private readonly HashSet<ReadSym> materialized = [];
    private readonly HashSet<PhiSym> phis = [];
    private readonly List<RecoveryHole> holes = [];
    private readonly Dictionary<ResultSym, Call> constructions = [];
    private readonly HashSet<Sym> absorbedChecks = [];
    private readonly Dictionary<Call, LocalValue> exceptions = new(ReferenceEqualityComparer.Instance);
    private IReadOnlyList<ExceptionRegionPlan> regions = [];
    private EffectAnalysis effects = null!;
    private IReadOnlyList<Block> order = [];
    private Block? currentBlock;
    private int nextLocal;

    private readonly InlineEvidence fields;
    private readonly TemplateRecovery templates;
    private readonly Dictionary<Variable, PendingConstruction> pendingConstructions = [];

    private BodyBuilder(MethodAnalysis analysis, TypeOracle oracle, TypeUsePlan uses, InlineEvidence fields, TemplateRecovery templates)
    {
        this.analysis = analysis;
        this.oracle = oracle;
        this.fields = fields;
        this.templates = templates;
        types = oracle.Types;
        values = analysis.Values;
        materialized.UnionWith(uses.Materialized);
    }

    public static LoweredBody Build(MethodAnalysis analysis, TypeOracle oracle, TypeUsePlan uses, InlineEvidence fields, TemplateRecovery templates) =>
        new BodyBuilder(analysis, oracle, uses, fields, templates).Run();

    private LoweredBody Run()
    {
        var function = analysis.Function;
        if (!ExceptionRegions.Build(function).TryGet(out var plan, out var failure))
            return new(null, [new(failure.Address, failure.Reason)], new Dictionary<Variable, PendingConstruction>(), 0);
        regions = plan.Regions;
        effects = new(values, oracle, regions);
        order = plan.Order;
        return LowerBlocks();
    }

    private LoweredBody LowerBlocks()
    {
        var function = analysis.Function;
        foreach (var region in regions.Where(r => r.BeginCatch is not null))
            exceptions[region.BeginCatch!] = NewLocal(types.Corlib("System.Exception"));
        var lowered = new List<(Block Block, List<ManagedStatement> Statements, Terminator? Exit)>();
        var holeRanges = new Dictionary<Block, (int From, int To)>();
        foreach (var block in order)
        {
            var output = new List<ManagedStatement>();
            Terminator? exit = null;
            currentBlock = block;
            var holesBefore = holes.Count;
            currentOutput = output;
            for (var i = 0; i < block.Statements.Count && exit is null; i++)
            {
                exit = Lower(block, i, output);
            }
            currentOutput = null;
            var normal = block.NormalSuccessors.ToArray();
            if (exit is null && output.LastOrDefault() is not (ManagedThrow or ManagedRethrow or ManagedReturn or ManagedEndFault or ManagedHole { Terminal: true }))
                exit = normal.Length == 1 ? new Jump(block.End, normal[0].Start) : Fail(block.End, "控制 块没有终结语句", terminal: true);
            lowered.Add((block, output, exit));
            holeRanges[block] = (holesBefore, holes.Count);
        }
        // 托管终结语句（不返回的抛出等）之后的机器块在 IL 中不可达：删去它们及其中的洞。
        var reachable = Reachable(lowered.Select(l => (l.Block, l.Exit)).ToArray());
        foreach (var (block, (from, to)) in holeRanges.OrderByDescending(p => p.Value.From))
            if (!reachable.Contains(block)) holes.RemoveRange(from, to - from);
        lowered.RemoveAll(l => !reachable.Contains(l.Block));
        // φ 的闭包：入边赋值的来源可能用到新的 φ。
        var done = new HashSet<PhiSym>();
        var copies = new Dictionary<(Block From, Block To, int Index), List<ManagedCopy>>();
        while (phis.Except(done).ToArray() is { Length: > 0 } pending)
            foreach (var phi in pending)
            {
                done.Add(phi);
                var local = locals[phi];
                for (var j = 0; j < phi.Block.Predecessors.Count; j++)
                {
                    var from = phi.Block.Predecessors[j];
                    var source = phi.Sources[j] is { } s ? View(s, local.Type, from.End) : Hole(from.End, "φ 来源缺失", local.Type);
                    if (!copies.TryGetValue((from, phi.Block, j), out var list)) copies[(from, phi.Block, j)] = list = [];
                    list.Add(new ManagedCopy(local, source));
                }
            }
        ManagedEdge Edge(Block from, ulong target)
        {
            var to = function.Blocks.FirstOrDefault(b => b.Start == target);
            if (to is null) return new ManagedEdge(target, []);
            var index = Enumerable.Range(0, to.Predecessors.Count).FirstOrDefault(j => to.Predecessors[j] == from, -1);
            return new ManagedEdge(target, index >= 0 && copies.TryGetValue((from, to, index), out var list) ? list : []);
        }
        var blocks = new List<ManagedBlock>();
        foreach (var (block, statements, exit) in lowered)
        {
            // 异常边的 φ 赋值放在可能抛出的语句之前：异常离开时局部已持有入边的值。
            if (block.Handler is { } pad && pad.Predecessors.IndexOf(block) is var padIndex and >= 0
                && copies.TryGetValue((block, pad, padIndex), out var exceptional) && exceptional.Count > 0)
            {
                var at = statements.FindLastIndex(s => s is ManagedCall or ManagedCheck or ManagedThrow);
                statements.InsertRange(at < 0 ? statements.Count : at, exceptional.Select(c => (ManagedStatement)new ManagedAssignment(block.End, c.Target, c.Value)));
            }
            switch (exit)
            {
                case Jump jump: statements.Add(new ManagedJump(jump.Address, Edge(block, jump.Target))); break;
                case Branch branch: statements.Add(new ManagedBranch(branch.Address, branch.Condition, Edge(block, branch.Target), Edge(block, branch.Fallthrough))); break;
                case Statement statement: statements.Add(statement.Value); break;
                case Switch table: statements.Add(new ManagedSwitch(table.Address, table.Index, table.Targets.Select(t => Edge(block, t)).ToArray())); break;
            }
            blocks.Add(new ManagedBlock(block.Start, statements));
        }
        foreach (var (result, _) in constructions.Where(p => !locals.ContainsKey(p.Key)))
            holes.Add(new RecoveryHole(result.Site.Address, "构造 分配后没有构造函数调用"));
        var managedRegions = regions.Where(r => reachable.Contains(r.Pad) && r.Try.Any(reachable.Contains)).Select(r => new ManagedRegion(
            r.Try.Where(reachable.Contains).Select(b => b.Start).ToArray(), r.Pad.Start, r.Handler.Where(reachable.Contains).Select(b => b.Start).ToArray(),
            r.BeginCatch is { } begin ? exceptions[begin] : null, r.IsCatch ? ManagedRegionKind.Catch : ManagedRegionKind.Fault)).ToArray();
        var body = ExceptionEntries.Run(new ManagedBody(analysis.Method, blocks) { Regions = managedRegions }, () => NewLocal(types.Int32));
        return new(body, holes.DistinctBy(h => (h.Address, h.Reason)).ToArray(), new Dictionary<Variable, PendingConstruction>(pendingConstructions), nextLocal);
    }

    /// <summary>沿托管终结语句的出边与区域的处理入口可达的块。</summary>
    private HashSet<Block> Reachable(IReadOnlyList<(Block Block, Terminator? Exit)> lowered)
    {
        var byStart = lowered.GroupBy(l => l.Block.Start).ToDictionary(g => g.Key, g => g.First());
        var reached = new HashSet<Block>();
        var work = new Stack<Block>();
        void Visit(ulong address)
        {
            if (byStart.TryGetValue(address, out var entry) && reached.Add(entry.Block)) work.Push(entry.Block);
        }
        Visit(lowered[0].Block.Start);
        while (work.Count > 0)
        {
            var block = work.Pop();
            var exit = byStart[block.Start].Exit;
            foreach (var target in exit switch
            {
                Jump j => [j.Target],
                Branch b => [b.Target, b.Fallthrough],
                Switch w => w.Targets,
                _ => Array.Empty<ulong>(),
            }) Visit(target);
            foreach (var region in regions.Where(r => r.Try.Contains(block))) Visit(region.Pad.Start);
        }
        return reached;
    }

    // ---- 终结语句 ----

    private abstract record Terminator;
    private sealed record Jump(ulong Address, ulong Target) : Terminator;
    private sealed record Branch(ulong Address, ManagedValue Condition, ulong Target, ulong Fallthrough) : Terminator;
    private sealed record Statement(ManagedStatement Value) : Terminator;
    private sealed record Switch(ulong Address, ManagedValue Index, ulong[] Targets) : Terminator;

    private Terminator Fail(ulong address, string reason, bool terminal)
    {
        holes.Add(new RecoveryHole(address, reason));
        return new Statement(new ManagedHole(address, reason, terminal));
    }

    private ManagedValue Hole(ulong address, string reason, TypeRef? type)
    {
        holes.Add(new RecoveryHole(address, reason));
        var t = type ?? types.Object;
        return new HoleValue(reason, t, Width(t));
    }

}
