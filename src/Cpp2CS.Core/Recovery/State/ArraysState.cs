using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class ArraysState : IStatementKeyed
{
    internal readonly Dictionary<Variable, Expr> arrayCursors = new();
    internal readonly Dictionary<Variable, Expr> arrayOffsets = new();
    internal readonly Dictionary<(Call Call, int Parameter), ArraySpan> arraySpans = [];

    public void Replace(Stmt previous, Stmt? replacement)
    {
        if (previous is not Call call) return;
        foreach (var item in arraySpans.Where(p => ReferenceEquals(p.Key.Call, call)).ToArray())
        {
            if (replacement is Call next) arraySpans[(next, item.Key.Parameter)] = item.Value;
            if (replacement is null or Nop) arraySpans.Remove(item.Key);
        }
    }
}
