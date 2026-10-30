
namespace Cpp2CS.Diagnostics;

public enum RewriteStatus { NoMatch, Blocked, Applied, Conflict }

/// <summary>规则证据只描述已检查的条件，不等同于执行验证。</summary>
public sealed record RuleEvidence(string Rule, IReadOnlyList<ulong> Sources, IReadOnlyList<string> Conditions);

public sealed record RuleTrace(string Rule, ulong Site, RewriteStatus Status, string? Code, string? Detail, RuleEvidence? Evidence);

/// <summary>候选识别与改写提交分开；拒绝携带稳定编号和具体说明。</summary>
public sealed record RewriteResult<T>(RewriteStatus Status, T? Value, string? Code, string? Detail, RuleEvidence? Evidence)
{
    public static RewriteResult<T> NoMatch() => new(RewriteStatus.NoMatch, default, null, null, null);
    public static RewriteResult<T> Blocked(string code, string detail) => new(RewriteStatus.Blocked, default, code, detail, null);
    public static RewriteResult<T> Applied(T value, RuleEvidence evidence) => new(RewriteStatus.Applied, value, null, null, evidence);
    public static RewriteResult<T> Conflict(string code, string detail) => new(RewriteStatus.Conflict, default, code, detail, null);
}
