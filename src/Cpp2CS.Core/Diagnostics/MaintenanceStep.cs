namespace Cpp2CS.Diagnostics;

/// <summary>
/// 一次维护动作或不动点组的诊断记录：所在步骤、动作、原因与前后的定义版本；
/// 不动点组另记轮数与收敛状态（Stable、BudgetExhausted）。
/// </summary>
public sealed record MaintenanceStep(string Step, string Action, string Reason, int InputVersion, int OutputVersion,
    int Rounds = 1, string? Convergence = null);
