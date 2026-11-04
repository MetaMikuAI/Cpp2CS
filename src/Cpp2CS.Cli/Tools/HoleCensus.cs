using System.Text.Json;
using System.Text.RegularExpressions;

namespace Cpp2CS.Cli;

/// <summary>汇总一次恢复的结果：决定下一步补什么时，按受影响方法数排序，而不是按样本。</summary>
internal static partial class HoleCensus
{
    public static int Run(string run, string[] options)
    {
        var top = options is ["--top", var count] ? int.Parse(count) : 40;
        var statuses = new Dictionary<string, int>();
        var first = new Dictionary<string, int>();
        var any = new Dictionary<string, int>();
        var attribution = new Dictionary<string, int>();
        var emit = new Dictionary<string, int>();
        foreach (var line in File.ReadLines(Path.Combine(run, "recovery.jsonl")))
        {
            using var document = JsonDocument.Parse(line);
            var method = document.RootElement;
            Add(statuses, method.GetProperty("status").GetString()!);
            if (method.GetProperty("emitProblem").GetString() is { } problem) Add(emit, Normalize(problem));
            var holes = method.GetProperty("holes").EnumerateArray().Select(h => Normalize(h.GetProperty("reason").GetString()!)).ToArray();
            if (holes.Length == 0) continue;
            Add(first, holes[0]);
            foreach (var reason in holes.Distinct()) Add(any, reason);
            if (method.TryGetProperty("rejections", out var rejections) && rejections.ValueKind == JsonValueKind.Array)
                foreach (var key in rejections.EnumerateArray().Select(r => $"{r.GetProperty("rule").GetString()}: {Normalize(r.GetProperty("reason").GetString()!)}").Distinct())
                    Add(attribution, key);
        }
        Console.WriteLine("状态：" + string.Join("，", statuses.OrderByDescending(p => p.Value).Select(p => $"{p.Key} {p.Value}")));
        Print("按方法的第一个洞", first, top);
        Print("按方法出现过的洞", any, top);
        Print("有洞方法的拒绝规则与运行时痕迹", attribution, top);
        Print("写出问题", emit, top);
        return 0;
    }

    private static void Add(Dictionary<string, int> counts, string key) => counts[key] = counts.GetValueOrDefault(key) + 1;

    private static void Print(string title, Dictionary<string, int> counts, int top)
    {
        Console.WriteLine($"\n## {title}（{counts.Count} 类，{counts.Values.Sum()} 次）");
        foreach (var (key, count) in counts.OrderByDescending(p => p.Value).Take(top))
            Console.WriteLine($"{count,7}  {key}");
    }

    /// <summary>去掉地址、标识符与符号值，只留原因的文字。</summary>
    private static string Normalize(string reason)
    {
        var text = Identifier().Replace(reason, "#");
        text = Repeated().Replace(text, "#");
        return text.Length <= 72 ? text : text[..72];
    }

    [GeneratedRegex(@"[A-Za-z0-9_<>`.\[\]{},:;+\-*!()@&|=/$'""~^%?\\φ]+")]
    private static partial Regex Identifier();

    [GeneratedRegex(@"#(\s*#)+")]
    private static partial Regex Repeated();
}
