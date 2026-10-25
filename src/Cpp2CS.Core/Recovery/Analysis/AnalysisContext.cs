using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Analysis;

/// <summary>
/// 方法级分析：只读准备结果（<see cref="MethodView"/>）与它所依赖的分析的结果，返回不可变的结果。
/// 依赖经 <see cref="AnalysisContext.Get{T}"/> 取得，第一次请求时才计算；同一个上下文里每个分析只算一次。
/// </summary>
internal interface IMethodAnalysis<out T> where T : class
{
    T Run(AnalysisContext context);
}

/// <summary>
/// 分析看到的 IR：保留的块（EH 未证明时只有正常边可达的块），以及 EH 已证明的 φ（筛去异常入边后的来源）。
/// 分析期间 IR 只读；改写 IR 的步骤（目前是帧区域的 <c>TypedFrame</c> 改写）之后要建新的上下文。
/// </summary>
internal sealed record MethodView(IReadOnlyList<Block> Blocks, IReadOnlyDictionary<Variable, Phi> ExceptionPhis)
{
    /// <summary>全部语句，φ 换成 EH 已证明的版本。</summary>
    public IEnumerable<Stmt> Statements => Blocks.SelectMany(b => b.Statements)
        .Select(s => s is Phi phi && ExceptionPhis.TryGetValue(phi.Target, out var proven) ? proven : s);
}

internal sealed class AnalysisContext(MethodView view)
{
    private readonly Dictionary<object, object> results = new(ReferenceEqualityComparer.Instance);
    private readonly HashSet<object> running = new(ReferenceEqualityComparer.Instance);

    public MethodView View { get; } = view;

    public T Get<T>(IMethodAnalysis<T> analysis) where T : class
    {
        if (results.TryGetValue(analysis, out var cached)) return (T)cached;
        if (!running.Add(analysis)) throw new InvalidOperationException($"分析 {analysis.GetType().Name} 的依赖成环");
        try
        {
            var result = analysis.Run(this);
            results[analysis] = result;
            return result;
        }
        finally { running.Remove(analysis); }
    }
}
