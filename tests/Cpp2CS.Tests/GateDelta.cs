using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace Cpp2CS.Tests;

/// <summary>前后比较的差异汇总：按类别计数，每类只打印前几条样例。失败类决定返回码，诊断类只报告。</summary>
internal sealed class DeltaLog(string name)
{
    private const int Samples = 12;
    private readonly SortedDictionary<string, (int Count, List<string> Examples)> failures = new(StringComparer.Ordinal);
    private readonly SortedDictionary<string, (int Count, List<string> Examples)> notes = new(StringComparer.Ordinal);

    public int Compared { get; set; }
    public bool Failed => failures.Count > 0;

    public void Fail(string category, string example) => Add(failures, category, example);
    public void Note(string category, string example) => Add(notes, category, example);

    private static void Add(SortedDictionary<string, (int Count, List<string> Examples)> table, string category, string example)
    {
        var (count, examples) = table.GetValueOrDefault(category, (0, new List<string>()));
        if (examples.Count < Samples) examples.Add(example);
        table[category] = (count + 1, examples);
    }

    public int Finish()
    {
        foreach (var (mark, table) in new[] { ("✗", failures), ("·", notes) })
            foreach (var (category, (count, examples)) in table)
            {
                Console.WriteLine($"{mark} {category}：{count} 处");
                foreach (var example in examples) Console.WriteLine($"    {example}");
            }
        Console.WriteLine(failures.Count == 0
            ? $"✓ {name}：比较 {Compared} 项，零差异{(notes.Count > 0 ? "；另有诊断差异（见上，不作判定）" : "")}"
            : $"✗ {name}：比较 {Compared} 项，差异 {failures.Values.Sum(v => v.Count)} 处");
        return failures.Count == 0 ? 0 : 1;
    }
}

/// <summary>jsonl 产物的读取与逐键比较。键为地址字段加方法名，保留文件次序。</summary>
internal static class Jsonl
{
    internal static readonly JsonSerializerOptions Json = new() { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };

    public sealed record Row(string Key, string Line, JsonObject Value);

    public static List<Row> Read(string directory, string file, string address = "address") =>
        File.ReadLines(Path.Combine(directory, file)).Where(l => l.Length > 0).Select(line =>
        {
            var value = JsonNode.Parse(line)!.AsObject();
            return new Row($"{value[address]}\t{value["method"]}", line, value);
        }).ToList();

    public static string Text(JsonNode? node) => node?.ToJsonString(Json) ?? "null";

    public static string Clip(string text, int limit = 160) => text.Length <= limit ? text : text[..limit] + "…";

    /// <summary>
    /// 逐键比较两份 jsonl：行集合、行次序与每行全部字段。整行文本相同即相同；不同时按顶层字段列出差异类别。
    /// </summary>
    public static void CompareKeyed(DeltaLog log, string file, string before, string after, string address = "address")
    {
        var left = Read(before, file, address);
        var right = Read(after, file, address);
        foreach (var (side, rows) in new[] { ("前", left), ("后", right) })
            foreach (var duplicate in rows.GroupBy(r => r.Key).Where(g => g.Count() > 1))
                log.Fail($"{file} 键重复（{side}）", duplicate.Key);
        var previous = left.GroupBy(r => r.Key).ToDictionary(g => g.Key, g => g.First());
        var current = right.GroupBy(r => r.Key).ToDictionary(g => g.Key, g => g.First());
        foreach (var key in previous.Keys.Except(current.Keys)) log.Fail($"{file} 丢失的行", key);
        foreach (var key in current.Keys.Except(previous.Keys)) log.Fail($"{file} 新增的行", key);
        var leftOrder = left.Select(r => r.Key).Where(current.ContainsKey).ToList();
        var rightOrder = right.Select(r => r.Key).Where(previous.ContainsKey).ToList();
        var divergence = leftOrder.Zip(rightOrder).TakeWhile(p => p.First == p.Second).Count();
        if (divergence < Math.Min(leftOrder.Count, rightOrder.Count))
            log.Fail($"{file} 行次序", $"第 {divergence} 行起不同：{leftOrder[divergence]} / {rightOrder[divergence]}");
        foreach (var key in leftOrder)
        {
            log.Compared++;
            var (l, r) = (previous[key], current[key]);
            if (l.Line == r.Line) continue;
            var fields = l.Value.Select(p => p.Key).Union(r.Value.Select(p => p.Key)).ToArray();
            var differing = fields.Where(f => Text(l.Value[f]) != Text(r.Value[f])).ToArray();
            if (differing.Length == 0) log.Fail($"{file} 字段次序或格式", key);
            foreach (var field in differing)
                log.Fail($"{file} 字段 {field}", $"{key}：{Clip(Text(l.Value[field]))} → {Clip(Text(r.Value[field]))}");
        }
    }
}

internal static class GateDelta
{
    [Command("publication-delta", "逐键比较 publication.jsonl：程序集、token 与 CIL 指纹，覆盖写出失败的骨架与部分体", Arguments = "<before> <after>")]
    public static int Publications(string before, string after)
    {
        var log = new DeltaLog("publication-delta");
        Jsonl.CompareKeyed(log, "publication.jsonl", before, after);
        return log.Finish();
    }

    /// <summary>
    /// 调用解析严格比较（第一部分包括 TypeVersion）；规则记录在映射改名后逐条比较；
    /// 分析步骤是诊断产物：序列差异只报告，但各步的 InputTypes、OutputTypes 序列必须一致。毫秒字段不比较。
    /// 映射文件每行“旧名&lt;Tab&gt;新名”，用于步骤与 pass 改名后对齐旧追踪。
    /// </summary>
    [Command("trace-delta", "比较 call-resolution（严格）、rules 与 analysis（按映射改名，忽略毫秒）", Arguments = "<before> <after> [--map 映射文件] [--ignore-type-version]")]
    public static int Trace(string before, string after, string[] options)
    {
        var map = new Dictionary<string, string>(StringComparer.Ordinal);
        var ignoreTypeVersion = false;
        for (var i = 0; i < options.Length; i++)
        {
            if (options[i] == "--ignore-type-version") ignoreTypeVersion = true;
            else if (options[i] == "--map" && i + 1 < options.Length)
                foreach (var line in File.ReadLines(options[++i]).Where(l => l.Length > 0 && !l.StartsWith('#')))
                {
                    var parts = line.Split('\t');
                    if (parts.Length != 2) throw new InvalidDataException($"映射行须为“旧名<Tab>新名”：{line}");
                    map.Add(parts[0], parts[1]);
                }
            else throw new ArgumentException($"未知或不完整的参数：{options[i]}");
        }
        var log = new DeltaLog("trace-delta");
        CompareGrouped(log, "call-resolution.jsonl", before, after, row =>
        {
            if (ignoreTypeVersion) row.Remove("TypeVersion");
            return row;
        }, failure: true);
        CompareGrouped(log, "rules.jsonl", before, after, row =>
        {
            if (row["Rule"]?.GetValue<string>() is { } rule && map.TryGetValue(rule, out var renamed)) row["Rule"] = renamed;
            return row;
        }, failure: true);
        CompareAnalysis(log, before, after, map);
        return log.Finish();
    }

    /// <summary>按“入口 + 方法”分组，组内保留记录次序逐条比较。</summary>
    private static void CompareGrouped(DeltaLog log, string file, string before, string after, Func<JsonObject, JsonObject> normalize, bool failure)
    {
        Dictionary<string, List<string>> Groups(string directory)
        {
            var groups = new Dictionary<string, List<string>>(StringComparer.Ordinal);
            foreach (var row in Jsonl.Read(directory, file, "entry"))
            {
                if (!groups.TryGetValue(row.Key, out var list)) groups[row.Key] = list = [];
                list.Add(Jsonl.Text(normalize(row.Value)));
            }
            return groups;
        }
        void Report(string category, string example)
        {
            if (failure) log.Fail(category, example);
            else log.Note(category, example);
        }
        var left = Groups(before);
        var right = Groups(after);
        foreach (var key in left.Keys.Union(right.Keys).Order(StringComparer.Ordinal))
        {
            log.Compared++;
            var l = left.GetValueOrDefault(key, []);
            var r = right.GetValueOrDefault(key, []);
            var same = l.Zip(r).TakeWhile(p => p.First == p.Second).Count();
            if (same == l.Count && same == r.Count) continue;
            Report($"{file} 记录", $"{key}：第 {same} 条起不同（{l.Count} → {r.Count} 条）："
                + $"{Jsonl.Clip(same < l.Count ? l[same] : "（无）")} → {Jsonl.Clip(same < r.Count ? r[same] : "（无）")}");
        }
    }

    /// <summary>
    /// 读取 analysis.jsonl 的步骤与 pass 序列，规范成与格式无关的文本：新格式是一条按完成先后排列的 trace，
    /// 旧格式是分开的 steps、passes。子步骤折叠进父步骤（父步骤的记录本身就是折叠后的值），不进入序列；
    /// 维护动作、不动点与规则位置只在两边都是新格式时作为时间线比较（诊断）。
    /// </summary>
    private static void CompareAnalysis(DeltaLog log, string before, string after, IReadOnlyDictionary<string, string> map)
    {
        static string Renamed(IReadOnlyDictionary<string, string> map, string? name) => name is not null && map.TryGetValue(name, out var renamed) ? renamed : name ?? "";
        string[] convergence = ["Single", "Stable", "BudgetExhausted"];
        string Convergence(JsonNode? value) => value is JsonValue v && v.TryGetValue<int>(out var index) ? convergence[index] : value?.ToString() ?? "";
        string Step(string? id, JsonObject s) => $"{Renamed(map, id)}|{s["InputVersion"]}|{s["OutputVersion"]}|{s["InputTypes"]}|{s["OutputTypes"]}|{s["StepKind"] ?? s["Kind"]}|{s["Invalidates"]}";
        string Pass(string? id, JsonObject p) => $"{Renamed(map, id)}|{p["Changed"]}|{p["InputStatements"]}|{p["OutputStatements"]}|{p["Rounds"]}|{Convergence(p["Convergence"])}";
        Dictionary<string, (string[] Steps, string[] Types, string[] Passes, string[]? Timeline)> Read(string directory) =>
            Jsonl.Read(directory, "analysis.jsonl", "entry").ToDictionary(row => row.Key, row =>
            {
                if (row.Value["trace"] is JsonArray trace)
                {
                    var entries = trace.Select(e => e!.AsObject()).ToArray();
                    var steps = entries.Where(e => e["Kind"]!.ToString() is "Step" or "1").ToArray();
                    var passes = entries.Where(e => e["Kind"]!.ToString() is "Pass" or "0").ToArray();
                    foreach (var entry in entries) entry.Remove("Milliseconds");
                    return (steps.Select(s => Step(s["Id"]?.GetValue<string>(), s)).ToArray(),
                        steps.Select(s => $"{s["InputTypes"]}/{s["OutputTypes"]}").ToArray(),
                        passes.Select(p => Pass(p["Id"]?.GetValue<string>(), p)).ToArray(),
                        entries.Select(e => Jsonl.Text(e)).ToArray());
                }
                var oldSteps = row.Value["steps"]!.AsArray().Select(s => s!.AsObject()).ToArray();
                var oldPasses = row.Value["passes"]!.AsArray().Select(p => p!.AsObject()).ToArray();
                return (oldSteps.Select(s => Step(s["Rule"]?.GetValue<string>(), s)).ToArray(),
                    oldSteps.Select(s => $"{s["InputTypes"]}/{s["OutputTypes"]}").ToArray(),
                    oldPasses.Select(p => Pass(p["Name"]?.GetValue<string>(), p)).ToArray(),
                    (string[]?)null);
            }, StringComparer.Ordinal);
        var left = Read(before);
        var right = Read(after);
        foreach (var key in left.Keys.Except(right.Keys)) log.Fail("analysis.jsonl 丢失的方法", key);
        foreach (var key in right.Keys.Except(left.Keys)) log.Fail("analysis.jsonl 新增的方法", key);
        foreach (var key in left.Keys.Intersect(right.Keys).Order(StringComparer.Ordinal))
        {
            log.Compared++;
            var (l, r) = (left[key], right[key]);
            if (!l.Types.SequenceEqual(r.Types))
                log.Fail("analysis.jsonl InputTypes/OutputTypes 序列", $"{key}：{Jsonl.Clip(string.Join(' ', l.Types))} → {Jsonl.Clip(string.Join(' ', r.Types))}");
            if (!l.Steps.SequenceEqual(r.Steps)) log.Note("analysis.jsonl 步骤序列（诊断）", $"{key}：{l.Steps.Length} → {r.Steps.Length} 步");
            if (!l.Passes.SequenceEqual(r.Passes)) log.Note("analysis.jsonl pass 序列（诊断）", $"{key}：{l.Passes.Length} → {r.Passes.Length} 个");
            if (l.Timeline is not null && r.Timeline is not null && !l.Timeline.SequenceEqual(r.Timeline))
                log.Note("analysis.jsonl 时间线（诊断）", $"{key}：{l.Timeline.Length} → {r.Timeline.Length} 条");
        }
    }

    /// <summary>facts-cache … cold 的两份输出（不同提交）逐字节比较；不同时列出 JSON 中不同的路径。</summary>
    [Command("facts-delta", "比较两个提交冷算的未注册事实与样本 CIL（facts-cache … cold 的输出目录）", Arguments = "<before> <after>")]
    public static int Facts(string before, string after)
    {
        var log = new DeltaLog("facts-delta");
        foreach (var file in new[] { "cold-facts.json", "cold-samples.json" })
        {
            log.Compared++;
            var left = File.ReadAllBytes(Path.Combine(before, file));
            var right = File.ReadAllBytes(Path.Combine(after, file));
            if (left.AsSpan().SequenceEqual(right)) continue;
            var paths = new List<string>();
            Differences(JsonNode.Parse(left), JsonNode.Parse(right), "$", paths);
            if (paths.Count == 0) log.Fail(file + " 格式", "JSON 相同而字节不同");
            foreach (var path in paths) log.Fail(file, path);
        }
        return log.Finish();
    }

    private static void Differences(JsonNode? left, JsonNode? right, string path, List<string> found)
    {
        if (found.Count >= 1000) return;
        switch (left, right)
        {
            case (JsonObject l, JsonObject r):
                foreach (var key in l.Select(p => p.Key).Union(r.Select(p => p.Key)))
                    Differences(l[key], r[key], $"{path}.{key}", found);
                return;
            case (JsonArray l, JsonArray r):
                if (l.Count != r.Count) found.Add($"{path}：长度 {l.Count} → {r.Count}");
                for (var i = 0; i < Math.Min(l.Count, r.Count); i++) Differences(l[i], r[i], $"{path}[{i}]", found);
                return;
            default:
                if (Jsonl.Text(left) != Jsonl.Text(right)) found.Add($"{path}：{Jsonl.Clip(Jsonl.Text(left), 80)} → {Jsonl.Clip(Jsonl.Text(right), 80)}");
                return;
        }
    }

    /// <summary>L2 普查（cpp2cs idioms）的两份输出逐项比较；idioms.txt 首行的耗时秒数不比较。</summary>
    [Command("census-delta", "比较两次 L2 普查的报告（idioms.txt、idiom-residuals.tsv、template-instances.jsonl）", Arguments = "<before> <after>")]
    public static int Census(string before, string after)
    {
        var log = new DeltaLog("census-delta");
        static string[] Lines(string directory, string file) => File.ReadAllLines(Path.Combine(directory, file)).Select(line =>
            System.Text.RegularExpressions.Regex.Replace(line, @"^(L2 惯用法普查：\d+ 个函数，)\d+ s；", "$1<耗时>；")).ToArray();
        foreach (var file in new[] { "idioms.txt", "idiom-residuals.tsv", "template-instances.jsonl" })
        {
            var (l, r) = (Lines(before, file), Lines(after, file));
            log.Compared += l.Length;
            var same = l.Zip(r).TakeWhile(p => p.First == p.Second).Count();
            if (same < l.Length || same < r.Length)
                log.Fail(file, $"第 {same + 1} 行起不同（{l.Length} → {r.Length} 行）：{Jsonl.Clip(same < l.Length ? l[same] : "（无）")} → {Jsonl.Clip(same < r.Length ? r[same] : "（无）")}");
        }
        return log.Finish();
    }

    /// <summary>
    /// 门禁运行中常开的计数器。非零不判失败，但要先查明原因：
    /// valueEqualStatementKeys 是值相等语句键的合并次数（O10 的依据）；baseHolesWithDerivedMarker 是原因文本带“（源于 ”标记的基础洞（4.13）。
    /// </summary>
    [Command("gate-counters", "读出一次 recover 的常开计数器（run.json 的 counters 与 recovery.jsonl 的洞原因）", Arguments = "<output>")]
    public static int Counters(string output)
    {
        var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(output, "run.json")))!;
        var marked = Jsonl.Read(output, "recovery.jsonl").SelectMany(row => row.Value["holes"]!.AsArray()
            .Where(h => h!["derived"]!.GetValue<bool>() == false && h["reason"]!.GetValue<string>().Contains("（源于 ", StringComparison.Ordinal))
            .Select(h => $"{row.Key} @ {h!["address"]}：{h["reason"]}")).ToArray();
        var counters = new JsonObject
        {
            ["valueEqualStatementKeys"] = manifest["counters"]?["valueEqualStatementKeys"]?.DeepClone(),
            ["baseHolesWithDerivedMarker"] = marked.Length,
        };
        Console.WriteLine(Jsonl.Text(counters));
        foreach (var example in marked.Take(12)) Console.WriteLine($"  {Jsonl.Clip(example, 240)}");
        return 0;
    }
}
