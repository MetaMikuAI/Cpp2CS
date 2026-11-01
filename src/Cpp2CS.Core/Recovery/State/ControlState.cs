using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>Control 族的证据：跳转表的下标与“判空吸收为虚调用”的调用。</summary>
internal sealed class ControlState : IStatementKeyed
{
    internal readonly Dictionary<IndirectJump, Expr> switchIndices = new(ReferenceEqualityComparer.Instance);
    internal readonly HashSet<Call> virtualCalls = new(ReferenceEqualityComparer.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(switchIndices, previous, replacement);
        StatementKeys.Replace(virtualCalls, previous, replacement);
    }
}
