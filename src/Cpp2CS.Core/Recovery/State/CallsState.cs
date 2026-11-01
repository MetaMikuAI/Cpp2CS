using Cpp2CS.Ir;
using Cpp2CS.Calls;

namespace Cpp2CS.Recovery;

internal sealed class CallsState : IStatementKeyed, IStatementInstances
{
    internal readonly HashSet<Call> cleanupCalls = new(StatementIdentity.Instance);
    internal readonly HashSet<ulong> cleanupSites = [];
    internal readonly HashSet<ulong> inlineCleanupSites = [];
    internal readonly CallBindingState callBindings = new();
    internal readonly Dictionary<Call, MethodRef> nativeImports = new(StatementIdentity.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(cleanupCalls, previous, replacement);
        StatementKeys.Replace(nativeImports, previous, replacement);
    }

    /// <summary>调用的解析结果随调用对象迁移（尾复制的各个副本各自解析）。</summary>
    public void Rewritten(Stmt previous, Stmt replacement)
    {
        if (previous is Call call && replacement is Call next) callBindings.Copy(call, next);
    }
}
