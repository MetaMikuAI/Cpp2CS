using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>
/// 步骤组：一个注册步骤按代码次序拆成的子步骤。子步骤继承父步骤的种类与只读检查；组内边界不挂接改写器、
/// 不刷新定义，只执行子步骤自己显式请求的维护动作。每个子步骤记一条追踪（前后的定义版本与语句数；已知类型数只记在父步骤上，内核不读类型表），
/// 父步骤的记录照旧由调度器写出，因此同组子步骤折叠后与原步骤的记录一致。组内数据由父步骤的局部变量传递。
/// </summary>
internal static class StepGroup
{
    /// <summary>运行一个子步骤。</summary>
    internal static void Run(RecoveryScope scope, string id, Action body) => Run(scope, id, () =>
    {
        body();
        return null;
    });

    /// <summary>运行一个可失败的子步骤；返回失败时由父步骤终止整组并按原步骤的方式记录失败。</summary>
    internal static RecoveryFailure? Run(RecoveryScope scope, string id, Func<RecoveryFailure?> body)
    {
        var parent = scope.currentStep;
        scope.currentStep = id;
        var (version, statements) = (scope.analyses.Version, Statements(scope));
        var started = System.Diagnostics.Stopwatch.GetTimestamp();
        var failure = body();
        var after = Statements(scope);
        scope.trace.Add(new(Cpp2CS.Diagnostics.TraceKind.SubStep, id, parent)
        {
            InputVersion = version,
            OutputVersion = scope.analyses.Version,
            Changed = !statements.SequenceEqual(after, ReferenceEqualityComparer.Instance),
            InputStatements = statements.Length,
            OutputStatements = after.Length,
            Milliseconds = System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds,
        });
        scope.currentStep = parent;
        return failure;
    }

    private static Stmt[] Statements(RecoveryScope scope) => scope.function.Blocks.SelectMany(b => b.Statements).ToArray();
}
