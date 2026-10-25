using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Analysis;

/// <summary>
/// 定义索引：每个 SSA 变量由哪条语句定义（Define 的值、φ、调用结果的第几项），φ 的来源在哪些 φ 中使用，
/// 以及数据流的依赖边（来源 → 用到它的定义），后者供洞的连带计算使用。顺序与语句顺序一致。
/// </summary>
internal sealed record Definitions(
    IReadOnlyDictionary<Variable, Expr> Values,
    IReadOnlyDictionary<Variable, Phi> Phis,
    IReadOnlyDictionary<Variable, (Call Call, int Index)> Results,
    IReadOnlyDictionary<Variable, IReadOnlyList<Phi>> PhiUses,
    IReadOnlyList<(Variable Source, Variable Target)> DataFlow)
{
    public static readonly Definitions Empty = new(new Dictionary<Variable, Expr>(), new Dictionary<Variable, Phi>(),
        new Dictionary<Variable, (Call, int)>(), new Dictionary<Variable, IReadOnlyList<Phi>>(), []);

    public static readonly IMethodAnalysis<Definitions> Analysis = new Analyzer();

    private sealed class Analyzer : IMethodAnalysis<Definitions>
    {
        public Definitions Run(AnalysisContext context)
        {
            var values = new Dictionary<Variable, Expr>();
            var phis = new Dictionary<Variable, Phi>();
            var results = new Dictionary<Variable, (Call, int)>();
            var phiUses = new Dictionary<Variable, List<Phi>>();
            foreach (var statement in context.View.Statements)
                switch (statement)
                {
                    case Define define: values[define.Target] = define.Value; break;
                    case Phi phi:
                        phis[phi.Target] = phi;
                        foreach (var source in phi.Sources)
                        {
                            if (!phiUses.TryGetValue(source, out var list)) phiUses[source] = list = [];
                            list.Add(phi);
                        }
                        break;
                    case Call call:
                        for (var i = 0; i < call.Defines.Length; i++)
                            if (call.Defines[i] is { } result) results[result] = (call, i);
                        break;
                }
            var flow = new List<(Variable, Variable)>();
            foreach (var (target, value) in values)
                foreach (var source in ExprMap.Walk(value).OfType<Use>().Select(u => u.Variable)) flow.Add((source, target));
            foreach (var (target, phi) in phis)
                foreach (var source in phi.Sources) flow.Add((source, target));
            return new(values, phis, results, phiUses.ToDictionary(p => p.Key, p => (IReadOnlyList<Phi>)p.Value), flow);
        }
    }
}
