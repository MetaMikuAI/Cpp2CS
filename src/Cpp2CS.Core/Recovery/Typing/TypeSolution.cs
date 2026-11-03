using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

internal enum TypeSolveState { Changed, Stable, Cycle, BudgetExceeded }

/// <summary>记录完整类型解；重复的非稳定状态和耗尽预算都不能当成收敛。</summary>
internal sealed class TypeSolution
{
    private const int MaxRounds = 64;
    private readonly List<IReadOnlyDictionary<PhiSym, TypeRef?>> history = [];
    public IReadOnlyDictionary<PhiSym, TypeRef?> Types { get; private set; } = new Dictionary<PhiSym, TypeRef?>();

    public TypeSolveState Accept(Dictionary<PhiSym, TypeRef?> next)
    {
        if (Same(Types, next)) return TypeSolveState.Stable;
        if (history.Any(previous => Same(previous, next))) return TypeSolveState.Cycle;
        if (history.Count >= MaxRounds) return TypeSolveState.BudgetExceeded;
        history.Add(Types);
        Types = new Dictionary<PhiSym, TypeRef?>(next);
        return TypeSolveState.Changed;
    }

    private static bool Same(IReadOnlyDictionary<PhiSym, TypeRef?> a, IReadOnlyDictionary<PhiSym, TypeRef?> b) =>
        a.Count == b.Count && a.All(p => b.TryGetValue(p.Key, out var type) && Equals(p.Value, type));
}
