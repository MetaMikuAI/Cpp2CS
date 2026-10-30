using Cpp2CS.Ir;
using Cpp2CS.Calls;

namespace Cpp2CS.Recovery;

internal sealed class CallsState : IStatementKeyed
{
    internal readonly HashSet<Call> cleanupCalls = new(ReferenceEqualityComparer.Instance);
    internal readonly HashSet<ulong> cleanupSites = [];
    internal readonly HashSet<ulong> inlineCleanupSites = [];
    internal readonly CallBindingState callBindings = new();
    internal readonly Dictionary<Call, MethodRef> nativeImports = new();
    internal readonly HashSet<ulong> sharedSites = [];
    internal readonly Dictionary<IndirectJump, Expr> switchIndices = new(ReferenceEqualityComparer.Instance);
    internal readonly Dictionary<Call, VirtualDelegate> virtualDelegates = new(ReferenceEqualityComparer.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(cleanupCalls, previous, replacement);
        StatementKeys.Replace(nativeImports, previous, replacement);
        StatementKeys.Replace(switchIndices, previous, replacement);
        StatementKeys.Replace(virtualDelegates, previous, replacement);
        if (previous is Call call && replacement is Call next) callBindings.Copy(call, next);
    }
}
