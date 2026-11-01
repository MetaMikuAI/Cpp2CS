using System.Diagnostics;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Algebra;

/// <summary>按声明顺序运行机器步骤；追踪不参与恢复判定。</summary>
internal sealed class PassList(MachineFunction function, List<PassStep> steps, StatementRewriter? rewriter = null)
{
    public void Run(string name, Action action) => Run(name, () => { action(); return 0; });

    public T Run<T>(string name, Func<T> action)
    {
        rewriter?.Attach(function);
        var before = Statements();
        var started = Stopwatch.GetTimestamp();
        var result = action();
        rewriter?.Attach(function);
        var after = Statements();
        steps.Add(new(name, !before.SequenceEqual(after, ReferenceEqualityComparer.Instance), before.Length, after.Length,
            1, PassConvergence.Single, Stopwatch.GetElapsedTime(started).TotalMilliseconds));
        return result;
    }

    public void Fixpoint(string name, int budget, Func<bool> round, Action cleanup)
    {
        var before = Statements();
        var started = Stopwatch.GetTimestamp();
        var rounds = 0;
        var stable = false;
        while (rounds < budget)
        {
            rounds++;
            if (!round()) { stable = true; break; }
            cleanup();
        }
        var after = Statements();
        steps.Add(new(name, !before.SequenceEqual(after, ReferenceEqualityComparer.Instance), before.Length, after.Length, rounds,
            stable ? PassConvergence.Stable : PassConvergence.BudgetExhausted, Stopwatch.GetElapsedTime(started).TotalMilliseconds));
    }

    private Stmt[] Statements() => function.Blocks.SelectMany(b => b.Statements).ToArray();
}
