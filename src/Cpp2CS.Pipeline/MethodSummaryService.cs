using Cpp2CS.Calls;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Pipeline;

/// <summary>会话拥有恢复器和摘要缓存；源码变换只读摘要，不启动恢复。</summary>
public sealed class MethodSummaryService
{
    private readonly Dictionary<MethodRequest, MethodRecoveryResult> summaries = [];
    private readonly Func<MethodRequest, MethodRecoveryResult> recover;
    public int Count => summaries.Count;
    public int DiscoveryRounds { get; private set; }
    public int AnalysisRuns { get; private set; }

    public MethodSummaryService(MethodRecovery recovery) : this(request => request.Mode switch
    {
        RecoveryMode.Definition => recovery.Recover(request.Method, request.Entry),
        RecoveryMode.Instance => recovery.RecoverInstance(request.Method, request.Entry),
        RecoveryMode.Shared => recovery.RecoverShared(request.Method, request.Entry),
        _ => throw new ArgumentOutOfRangeException(nameof(request)),
    }) { }

    internal MethodSummaryService(Func<MethodRequest, MethodRecoveryResult> recover) => this.recover = recover;

    public void Seed(RecoveryTarget target, MethodRecoveryResult result) => summaries.TryAdd(
        new(target.Instance, target.Entry, target.Shared ? RecoveryMode.Shared : RecoveryMode.Definition), result);

    public MethodRecoveryResult Recover(MethodRef method, ulong entry) => Get(new(method, entry));
    public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => Get(new(method, entry, RecoveryMode.Instance));

    private MethodRecoveryResult Get(MethodRequest request)
    {
        if (summaries.TryGetValue(request, out var known)) return known;
        var result = recover(request);
        summaries.Add(request, result);
        return result;
    }

    public T Complete<T>(Func<IMethodSummaries, T> analyze) => Complete([0], (_, catalog) => analyze(catalog))[0];

    /// <summary>只重放读取了缺失摘要的方法；已完成结果与摘要失败结果均可复用。</summary>
    public Dictionary<TKey, T> Complete<TKey, T>(IReadOnlyList<TKey> items, Func<TKey, IMethodSummaries, T> analyze) where TKey : notnull
    {
        var results = new Dictionary<TKey, T>();
        var dirty = items.ToArray();
        while (dirty.Length != 0)
        {
            var blocked = new List<TKey>();
            var pending = new HashSet<MethodRequest>();
            foreach (var item in dirty)
            {
                var reader = new Reader(summaries);
                results[item] = analyze(item, reader);
                AnalysisRuns++;
                if (reader.Missing.Count == 0) continue;
                blocked.Add(item);
                pending.UnionWith(reader.Missing);
            }
            if (pending.Count == 0) break;
            DiscoveryRounds++;
            foreach (var request in pending.OrderBy(r => r.Method.Method.Index).ThenBy(r => r.Entry).ThenBy(r => r.Mode).ToArray())
                Get(request);
            dirty = blocked.ToArray();
        }
        return results;
    }

    private sealed class Reader(IReadOnlyDictionary<MethodRequest, MethodRecoveryResult> summaries) : IMethodSummaries
    {
        public HashSet<MethodRequest> Missing { get; } = [];
        public MethodRecoveryResult? Find(MethodRequest request)
        {
            if (summaries.TryGetValue(request, out var result)) return result;
            Missing.Add(request);
            return null;
        }
    }
}
