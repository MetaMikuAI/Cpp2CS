namespace Cpp2CS.Tests.Execution;

internal enum ExecutionVerdict { Verified, Partial, Mismatch, NotCheckable, NotWritten }

internal static class ExecutionVerdicts
{
    public static ExecutionVerdict Classify(int requested, int matches, int mismatches) => mismatches > 0
        ? ExecutionVerdict.Mismatch : matches == requested && requested > 0 ? ExecutionVerdict.Verified
        : matches > 0 ? ExecutionVerdict.Partial : ExecutionVerdict.NotCheckable;

    public static string Label(this ExecutionVerdict verdict) => verdict switch
    {
        ExecutionVerdict.Verified => "verified",
        ExecutionVerdict.Partial => "partial",
        ExecutionVerdict.Mismatch => "mismatch",
        ExecutionVerdict.NotCheckable => "not-checkable",
        ExecutionVerdict.NotWritten => "not-written",
        _ => throw new ArgumentOutOfRangeException(nameof(verdict)),
    };

    /// <summary>0：全部请求用例通过；1：存在差异；3：验证不完整（含空清单）。</summary>
    public static int ExitCode(IEnumerable<ExecutionVerdict> verdicts)
    {
        var all = verdicts.ToArray();
        return all.Contains(ExecutionVerdict.Mismatch) ? 1
            : all.Length > 0 && all.All(v => v == ExecutionVerdict.Verified) ? 0 : 3;
    }
}
