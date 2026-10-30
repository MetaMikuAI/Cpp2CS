using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Analysis;

/// <summary>一次分析读取的语句与控制流版本；节点保留原生地址，语句序列固定。</summary>
internal sealed class MethodSnapshot
{
    private readonly (ulong Start, ulong End, int Index, Block? Handler, bool LandingPad, ulong[] Successors, ulong[] Predecessors, Stmt[] Statements)[] blocks;
    private readonly KeyValuePair<Variable, Phi>[] exceptionPhis;
    private readonly List<Func<bool>> unchanged = [];

    public int Version { get; }
    public MethodView View { get; }

    public MethodSnapshot(int version, IReadOnlyList<Block> blocks, IReadOnlyDictionary<Variable, Phi> exceptionPhis)
    {
        Version = version;
        this.blocks = blocks.Select(b => (b.Start, b.End, b.Index, b.Handler, b.IsLandingPad,
            b.Successors.Select(s => s.Start).ToArray(), b.Predecessors.Select(s => s.Start).ToArray(), b.Statements.ToArray())).ToArray();
        this.exceptionPhis = exceptionPhis.ToArray();
        foreach (var statement in this.blocks.SelectMany(b => b.Statements).Concat(exceptionPhis.Values).Distinct(ReferenceEqualityComparer.Instance).Cast<Stmt>())
        {
            switch (statement)
            {
                case Phi phi: Watch(phi.Sources); break;
                case Call call: Watch(call.Arguments); Watch(call.Sources); Watch(call.Results); Watch(call.Defines); break;
                case IndirectJump jump: Watch(jump.Targets); break;
                case Return returned: Watch(returned.Pieces); break;
            }
            foreach (var intrinsic in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Intrinsic>()) Watch(intrinsic.Arguments);
        }
        View = new(blocks, exceptionPhis);
    }

    private void Watch<T>(T[] values)
    {
        var original = values.ToArray();
        unchanged.Add(() => original.SequenceEqual(values));
    }

    // 节点发布后必须整体替换；原地改数组会同时破坏旧快照和基于它的缓存。
    public void Validate()
    {
        if (unchanged.Any(check => !check())) throw new InvalidOperationException("已发布的 IR 节点被原地修改；请替换节点并刷新方法快照");
    }

    public bool Matches(IReadOnlyList<Block> current, IReadOnlyDictionary<Variable, Phi> phis)
    {
        Validate();
        return blocks.Length == current.Count && blocks.Zip(current).All(p => p.First.Start == p.Second.Start && p.First.End == p.Second.End
            && ReferenceEquals(p.First.Handler, p.Second.Handler) && p.First.LandingPad == p.Second.IsLandingPad
            && p.First.Predecessors.SequenceEqual(p.Second.Predecessors.Select(s => s.Start))
            && p.First.Index == p.Second.Index && p.First.Successors.SequenceEqual(p.Second.Successors.Select(s => s.Start))
            && p.First.Statements.SequenceEqual(p.Second.Statements, ReferenceEqualityComparer.Instance))
        && exceptionPhis.Length == phis.Count && exceptionPhis.All(p => phis.TryGetValue(p.Key, out var value) && ReferenceEquals(value, p.Value));
    }
}

/// <summary>IR 变化后失效全部方法分析；同一快照内按需复用。</summary>
internal sealed class MethodAnalyses
{
    private AnalysisContext? context;
    public MethodSnapshot? Snapshot { get; private set; }
    public int Version => Snapshot?.Version ?? 0;

    public bool Refresh(IReadOnlyList<Block> blocks, IReadOnlyDictionary<Variable, Phi> phis)
    {
        if (Snapshot?.Matches(blocks, phis) == true) return false;
        Snapshot = new(Version + 1, blocks, phis);
        context = new(Snapshot.View);
        return true;
    }

    public T Get<T>(IMethodAnalysis<T> analysis) where T : class =>
        (context ?? throw new InvalidOperationException("尚未建立方法快照")).Get(analysis);
}
