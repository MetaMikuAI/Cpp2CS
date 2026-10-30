using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class ExceptionsState : IStatementKeyed
{
    internal ExceptionLayout? exceptionLayout;
    internal readonly Dictionary<ExceptionRegionPlan, LocalValue> caughtExceptions = [];
    internal readonly Dictionary<Variable, LocalValue> exceptionValues = [];
    internal readonly Dictionary<Variable, LocalValue> wrappers = [];
    internal readonly Dictionary<Call, TypeRef> exceptionTypeTargets = new(ReferenceEqualityComparer.Instance);
    internal readonly Dictionary<Variable, Phi> exceptionPhis = [];
    internal readonly HashSet<Variable> exceptionDemand = [];
    internal bool collectingExceptionDemand;

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(exceptionTypeTargets, previous, replacement);
    }
}
