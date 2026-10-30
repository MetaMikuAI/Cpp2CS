
namespace Cpp2CS.Diagnostics;

public enum IterationStatus { Stable, Cycle, BudgetExceeded }
public sealed record IterationResult<T>(T Value, int Rounds, IterationStatus Status);

/// <summary>有限迭代；稳定、重复状态与预算耗尽分别报告。</summary>
public static class Iteration
{
    public static IterationResult<T> Run<T>(T initial, Func<T, T> step, Func<T, T, bool> same, int budget)
    {
        if (budget < 1) throw new ArgumentOutOfRangeException(nameof(budget));
        var history = new List<T> { initial };
        var current = initial;
        for (var round = 1; round <= budget; round++)
        {
            var next = step(current);
            if (same(current, next)) return new(next, round, IterationStatus.Stable);
            if (history.Any(previous => same(previous, next))) return new(next, round, IterationStatus.Cycle);
            history.Add(next);
            current = next;
        }
        return new(current, budget, IterationStatus.BudgetExceeded);
    }
}
