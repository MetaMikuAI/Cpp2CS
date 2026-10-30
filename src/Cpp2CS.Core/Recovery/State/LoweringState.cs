using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class LoweringState : IStatementKeyed
{
    internal readonly HashSet<Stmt> dropped = new(ReferenceEqualityComparer.Instance);
    /// <summary>内联到使用处的定义（见类注释第 8 条）。</summary>
    internal readonly HashSet<Variable> inlined = [];

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(dropped, previous, replacement);
    }
}
