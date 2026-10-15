using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>逐 case 检查托管表达式；保留全部失败原因，不以表达式完整代替方法体生成。</summary>
internal static class ValuesRun
{
    public static int Run(string binary, string metadata, string output, string? selector)
    {
        var model = ModelCheck.Load(binary, metadata);
        var session = new RecoverySession(model);
        var namespaces = selector?.Split(',') ?? ["Sekai.Mysekai", "Sekai.Api"];
        var cases = Corpus.Cases(model, namespaces);
        var directory = Path.GetDirectoryName(Path.GetFullPath(output))!;
        Directory.CreateDirectory(directory);
        using var report = new StreamWriter(output);
        var reasons = new Dictionary<string, int>();
        var watch = Stopwatch.StartNew();
        int preparedCount = 0, expressionComplete = 0, recovered = 0, missing = 0;
        foreach (var (address, method) in cases)
        {
            var problems = new List<(ulong Address, string Reason)>();
            int good = 0, bad = 0;
            void Problem(ulong at, string? reason)
            {
                var text = reason ?? "未说明的恢复缺口";
                problems.Add((at, text));
                bad++;
                var category = text.Split(':')[0];
                if (text.StartsWith("未确定变量")) category = "未确定变量";
                if (text.StartsWith("字段位置未匹配")) category = "字段位置未匹配";
                if (text.StartsWith("变量 ")) category = "变量位宽不符";
                if (text.StartsWith("值类型不符")) category = "值类型不符";
                reasons[category] = reasons.GetValueOrDefault(category) + 1;
            }
            if (session.Functions.At(address) is not { } range || range.Start != address) Problem(address, "没有函数边界");
            else
            {
                var prepared = session.Analyze(method, address, range);
                foreach (var error in prepared.Problems) Problem(address, error);
                if (prepared.Problems.Count == 0)
                {
                    preparedCount++;
                    var values = new ValueRecovery(session, prepared);
                    foreach (var stackProblem in values.Stack.Problems) Problem(stackProblem.Address, stackProblem.Reason);
                    foreach (var bufferProblem in values.BufferProblems) Problem(bufferProblem.Address, bufferProblem.Reason);
                    var copies = TypedCopies.Recover(prepared.Function, values, session.Types);
                    if (values.SignatureProblem is { } signatureProblem) Problem(address, "入口 ABI: " + signatureProblem);
                    var returnType = method.Method.ReturnType.Substitute(method.TypeArguments, method.MethodArguments);
                    foreach (var block in prepared.Function.Blocks)
                    {
                        if (block.IsLandingPad || block.Handler is not null) Problem(block.Start, "异常区域尚未恢复");
                        foreach (var stmt in block.Statements)
                        {
                            if (copies.ContainsKey(stmt)) { good++; continue; }
                            string? problem = null;
                            var accepted = stmt switch
                            {
                                Define d => values.Recover(d.Value, out problem) is not null,
                                Phi p => values.Locals.ContainsKey(p.Target),
                                Store s => Store(s, values, out problem),
                                Call c => values.Invocation(c, out problem) is not null,
                                Branch b => values.Recover(b.Condition, out problem) is not null,
                                Return { Buffer: not null } => values.ReturnValue is not null,
                                Return { Pieces.Length: > 0 } r => values.Aggregate(returnType, r.Pieces, out problem) is not null,
                                Return { Value: { } v } => values.RecoverAs(v, returnType, out problem) is not null,
                                Return or Jump or Nop => true,
                                _ => Unsupported($"未支持语句 {stmt.GetType().Name}", out problem),
                            };
                            if (accepted) good++;
                            else Problem(stmt.Address, problem ?? (stmt is Phi ? "汇合值类型未确定" : null));
                        }
                    }
                }
            }
            recovered += good;
            missing += bad;
            if (bad == 0) expressionComplete++;
            report.WriteLine(JsonSerializer.Serialize(new
            {
                address = $"0x{address:x}", methodIndex = method.Method.Index, method = method.ToString(),
                signature = $"{method.Method.ReturnType} ({string.Join(", ", method.Method.Parameters.Select(p => p.Type.ToString()))})",
                expressionsComplete = bad == 0, recoveredStatements = good,
                problems = problems.Select(p => new { address = $"0x{p.Address:x}", reason = p.Reason }),
            }));
        }
        Console.WriteLine($"case {cases.Count}  准备通过 {preparedCount}  表达式完整 {expressionComplete}  未完整 {cases.Count - expressionComplete}");
        Console.WriteLine($"已恢复语句 {recovered}  缺口 {missing}  用时 {watch.ElapsedMilliseconds} ms");
        foreach (var (reason, count) in reasons.OrderByDescending(p => p.Value).Take(20)) Console.WriteLine($"  {count,8} {reason}");
        Console.WriteLine("表达式检查不等于方法体输出或运行时行为验证");
        return cases.Count > 0 && expressionComplete == cases.Count ? 0 : 1;
    }

    private static bool Store(Store store, ValueRecovery values, out string? problem)
    {
        if (values.Location(store.Target, store.Value.Width, out problem) is not { } target) return false;
        return values.RecoverAs(store.Value, target.Type, out problem) is not null;
    }
    private static bool Unsupported(string reason, out string? problem) { problem = reason; return false; }
}
