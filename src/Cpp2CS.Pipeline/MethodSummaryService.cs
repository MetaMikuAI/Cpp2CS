using Cpp2CS.Calls;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Pipeline;

/// <summary>会话拥有恢复器和摘要缓存；源码变换只读摘要，不启动恢复。</summary>
public sealed class MethodSummaryService(MethodRecovery recovery) : IMethodSummaries
{
    private readonly Dictionary<MethodRequest, MethodRecoveryResult> summaries = [];
    private readonly HashSet<MethodRequest> pending = [];
    public int Count => summaries.Count;
    public int DiscoveryRounds { get; private set; }

    public MethodRecoveryResult? Find(MethodRequest request)
    {
        if (summaries.TryGetValue(request, out var result)) return result;
        pending.Add(request);
        return null;
    }

    public MethodRecoveryResult Recover(MethodRef method, ulong entry) => Get(new(method, entry));
    public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => Get(new(method, entry, RecoveryMode.Instance));

    private MethodRecoveryResult Get(MethodRequest request)
    {
        if (summaries.TryGetValue(request, out var known)) return known;
        var result = request.Mode switch
        {
            RecoveryMode.Definition => recovery.Recover(request.Method, request.Entry),
            RecoveryMode.Instance => recovery.RecoverInstance(request.Method, request.Entry),
            RecoveryMode.Shared => recovery.RecoverShared(request.Method, request.Entry),
            _ => throw new ArgumentOutOfRangeException(nameof(request)),
        };
        summaries.Add(request, result);
        return result;
    }

    public T Complete<T>(Func<IMethodSummaries, T> analyze)
    {
        while (true)
        {
            pending.Clear();
            var result = analyze(this);
            if (pending.Count == 0) return result;
            DiscoveryRounds++;
            foreach (var request in pending.OrderBy(r => r.Method.Method.Index).ThenBy(r => r.Entry).ThenBy(r => r.Mode).ToArray())
                Get(request);
        }
    }
}
