using Cpp2CS.Facts;
using Cpp2CS.Input;

namespace Cpp2CS.Tests;

/// <summary>在真实映像上建立基础事实：所有 Error 级不变式必须成立；Warning 只列出不判失败。</summary>
internal static class FactsCheck
{
    [Command("facts", "基础事实不变式：不得有 Error 级违例", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var a = new Assertions();
        foreach (var check in facts.Checks.All.Where(c => c.Severity == "Error"))
            a.True(check.Passed, $"{check.Name}：{check.Violations}/{check.Total} 违例，例如 {string.Join("；", check.Samples.Take(3))}");
        a.True(facts.Unregistered.All.All(d => d.ShapeMatches.Count > 0 && d.Witnesses.Count > 0
            && d.Witnesses.All(w => w.Instance.Method == d.Definition && UnregisteredMethods.IsClosed(w.Instance))),
            "F8 证据完整，正见证封闭且定义一致");
        foreach (var check in facts.Checks.All.Where(c => c.Severity == "Warning" && !c.Passed))
            Console.WriteLine($"! {check.Name}：{check.Violations}/{check.Total}（已知缺口）");
        Execution.LsdaCheck.Compare(facts, a);
        return a.Finish("facts");
    }
}
