using Cpp2CS.Ir;
using Cpp2CS.Calls;

namespace Cpp2CS.Recovery;

internal sealed class CallsState : IStatementKeyed
{
    internal readonly HashSet<Call> cleanupCalls = new(ReferenceEqualityComparer.Instance);
    internal readonly HashSet<ulong> cleanupSites = [];
    internal readonly HashSet<ulong> inlineCleanupSites = [];
    internal readonly CallBindingState callBindings = new();
    internal readonly Dictionary<Call, MethodRef> nativeImports = new(ReferenceEqualityComparer.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(cleanupCalls, previous, replacement);
        StatementKeys.Replace(nativeImports, previous, replacement);
        if (previous is Call call && replacement is Call next) callBindings.Copy(call, next);
    }
}
