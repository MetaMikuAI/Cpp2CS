using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class RuntimeState : IStatementKeyed
{
    internal readonly HashSet<Variable> runtime = [];
    internal readonly Dictionary<Variable, Use> objectClasses = new();
    internal readonly Dictionary<Call, Use> typeChecks = new(ReferenceEqualityComparer.Instance);
    /// <summary>经虚表读取得到的委托目标。</summary>
    internal readonly Dictionary<Call, VirtualDelegate> virtualDelegates = new(ReferenceEqualityComparer.Instance);
    // ---------- 值恢复 ----------
    internal NullPathFacts? nullPaths;
    internal readonly HashSet<Call> genericResolvers = new(ReferenceEqualityComparer.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(typeChecks, previous, replacement);
        StatementKeys.Replace(virtualDelegates, previous, replacement);
        StatementKeys.Replace(genericResolvers, previous, replacement);
    }
}
