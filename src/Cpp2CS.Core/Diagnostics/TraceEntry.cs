namespace Cpp2CS.Diagnostics;

/// <summary>追踪记录的种类。</summary>
public enum TraceKind
{
    /// <summary>Prepare 的条目或 L2 的 pass：前后语句数与是否改动。</summary>
    Pass,
    /// <summary>Analyze 的注册步骤：前后的定义版本与已知类型数。</summary>
    Step,
    /// <summary>维护动作：所在步骤、原因 Id 与前后的定义版本。</summary>
    Maintenance,
    /// <summary>不动点组：轮数与收敛状态。</summary>
    Fixpoint,
    /// <summary>规则的应用、阻断或冲突，带证据。</summary>
    Rule,
}

/// <summary>
/// 方法恢复追踪中的一条记录，按完成的先后排列（嵌套的记录先于外层）。诊断产物，不参与恢复判定。
/// <paramref name="Id"/> 是步骤、pass、维护动作、不动点组或规则的名字；<paramref name="Step"/> 是记录发生时所在的步骤。
/// 其余字段按种类取用，不适用的为空。
/// </summary>
public sealed record TraceEntry(TraceKind Kind, string Id, string Step)
{
    /// <summary>维护动作的原因 Id。</summary>
    public string? Reason { get; init; }
    /// <summary>Analyze 步骤的种类（analysis、machine-pass）与改写步骤声明的失效范围。</summary>
    public string? StepKind { get; init; }
    public string? Invalidates { get; init; }
    public int? InputVersion { get; init; }
    public int? OutputVersion { get; init; }
    public int? InputTypes { get; init; }
    public int? OutputTypes { get; init; }
    public bool? Changed { get; init; }
    public int? InputStatements { get; init; }
    public int? OutputStatements { get; init; }
    public int? Rounds { get; init; }
    public string? Convergence { get; init; }
    public RuleTrace? Rule { get; init; }
    public double? Milliseconds { get; init; }

    public static TraceEntry Of(PassStep pass, string step) => new(TraceKind.Pass, pass.Name, step)
    {
        Changed = pass.Changed,
        InputStatements = pass.InputStatements,
        OutputStatements = pass.OutputStatements,
        Rounds = pass.Rounds,
        Convergence = pass.Convergence.ToString(),
        Milliseconds = pass.Milliseconds,
    };
}
