using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery;

/// <summary>诊断：CPP2CS_TYPING_TRACE=0x入口[,0x入口…] 时打印最后一轮的全部约束与解（stderr）。不参与推断。</summary>
internal sealed class TraceContributor(DiagnosticOptions diagnostics, ulong entry) : ITypeContributor
{
    private TypeConstraints last = new();
    public string Name => "诊断";

    public void Contribute(TypingContext context, TypeConstraints constraints) => last = constraints;
    public void Print(Dictionary<Variable, TypeResult> solution, int rounds)
    {
        diagnostics.Write("typing", entry, $"引擎 {rounds} 轮");
        foreach (var v in last.Variables.Concat(solution.Keys).Distinct().OrderBy(v => v.ToString(), StringComparer.Ordinal))
        {
            diagnostics.Write("typing", entry, $"  {v} = {solution.GetValueOrDefault(v)?.ToString() ?? "未知"}");
            foreach (var (type, evidence) in last.Definitions.GetValueOrDefault(v) ?? [])
                diagnostics.Write("typing", entry, $"    定义 {type}  {evidence}");
            foreach (var (type, evidence) in last.Uses.GetValueOrDefault(v) ?? [])
                diagnostics.Write("typing", entry, $"    使用 {type}  {evidence}");
            foreach (var (source, evidence) in last.FlowEdges.GetValueOrDefault(v) ?? [])
                diagnostics.Write("typing", entry, $"    来自 {source}  {evidence}");
        }
    }
}
