using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class RuntimeState : IStatementKeyed
{
    internal readonly HashSet<Variable> runtime = [];
    internal readonly Dictionary<Variable, Use> objectClasses = new();
    internal readonly Dictionary<Call, Use> typeChecks = new(ReferenceEqualityComparer.Instance);
    internal readonly HashSet<Call> virtualCalls = new(ReferenceEqualityComparer.Instance);
    // ---------- 值恢复 ----------
    internal NullPathFacts? nullPaths;
    internal readonly HashSet<Call> genericResolvers = new(ReferenceEqualityComparer.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(typeChecks, previous, replacement);
        StatementKeys.Replace(virtualCalls, previous, replacement);
        StatementKeys.Replace(genericResolvers, previous, replacement);
    }
}
