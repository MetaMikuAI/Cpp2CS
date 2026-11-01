
namespace Cpp2CS.Facts;

/// <summary>
/// 一条事实不变式的检查结果。Violations 为违反条数，Total 为检查的总条数；Samples 最多给出若干违例。
/// Severity：Error 表示事实不可信（后续层不得依赖），Warning 表示已知缺口，Info 只做记录。
/// </summary>
public sealed record FactCheck(string Name, string Severity, long Total, long Violations, string Detail, IReadOnlyList<string> Samples)
{
    public bool Passed => Violations == 0;
}

public sealed class FactChecks
{
    private readonly List<FactCheck> checks = [];
    public IReadOnlyList<FactCheck> All => checks;

    internal void Add(FactCheck check) => checks.Add(check);

    public void Add(string name, string severity, long total, IReadOnlyCollection<string> violations, string detail, int samples = 12) =>
        checks.Add(new(name, severity, total, violations.Count, detail, violations.Take(samples).ToArray()));

    public void Info(string name, long total, string detail) => checks.Add(new(name, "Info", total, 0, detail, []));

    public bool AnyErrors => checks.Any(c => c.Severity == "Error" && !c.Passed);
}
