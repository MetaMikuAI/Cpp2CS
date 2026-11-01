using System.Reflection;

namespace Cpp2CS.Tests.Architecture;

/// <summary>
/// 结构约束的账本文件（tests/Cpp2CS.Tests/Architecture/*.tsv）：棘轮、白名单、豁免清单、族归属快照、注册表快照与洞编码清单。
/// 治理规则见主文 3.3：棘轮只降不升，下降当次写回；白名单与豁免清单的新增单独成提交并经用户确认；快照的改动随代码提交并列出差异。
/// </summary>
internal static class Ledgers
{
    public static string Folder(string repository) => Path.Combine(repository, "tests", "Cpp2CS.Tests", "Architecture");

    // ---------- 棘轮 ----------

    public static SortedDictionary<string, int> ReadRatchet(string path) => new(File.ReadLines(path)
        .Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t')).ToDictionary(f => f[0], f => int.Parse(f[1])), StringComparer.Ordinal);

    public static void WriteRatchet(string path, IReadOnlyDictionary<string, int> values) => File.WriteAllLines(path,
        new[] { "# 计数项/范围\t记录值。只降不升：当前值低于记录值时同一提交内写回（architecture <repo> --write）；上调须经用户确认。" }
            .Concat(values.Where(p => p.Value > 0).OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => $"{p.Key}\t{p.Value}")));

    /// <summary>当前值与记录值逐键比较；未记录的键按 0 计。</summary>
    public static void CheckRatchet(IReadOnlyDictionary<string, int> recorded, IReadOnlyDictionary<string, int> current, List<string> failures)
    {
        foreach (var key in recorded.Keys.Union(current.Keys).Order(StringComparer.Ordinal))
        {
            var (was, now) = (recorded.GetValueOrDefault(key), current.GetValueOrDefault(key));
            if (now > was) failures.Add($"棘轮上升 {key}：{was} → {now}");
            else if (now < was) failures.Add($"棘轮下降未写回 {key}：{was} → {now}（运行 architecture <repo> --write）");
        }
    }

    // ---------- 白名单与豁免清单 ----------

    public sealed record Entry(string Tag, string Member, string Location, string Package, string Expiry, string Reason)
    {
        public bool Covers(Access access) => access.Tag == Tag && access.Member == Member
            && (access.File == Location || access.File.StartsWith(Location.TrimEnd('/') + "/", StringComparison.Ordinal));
    }

    private const string EntryHeader = "# 约束标签\t成员\t位置（文件或目录）\t工作包\t到期里程碑\t理由";

    public static List<Entry> ReadEntries(string path) => File.ReadLines(path).Where(l => l.Length > 0 && !l.StartsWith('#'))
        .Select(l => l.Split('\t')).Select(f => new Entry(f[0], f[1], f[2], f[3], f[4], f[5])).ToList();

    public static void WriteEntries(string path, IEnumerable<Entry> entries) => File.WriteAllLines(path, new[] { EntryHeader }
        .Concat(entries.OrderBy(e => e.Tag, StringComparer.Ordinal).ThenBy(e => e.Location, StringComparer.Ordinal).ThenBy(e => e.Member, StringComparer.Ordinal)
            .Select(e => $"{e.Tag}\t{e.Member}\t{e.Location}\t{e.Package}\t{e.Expiry}\t{e.Reason}")));

    /// <summary>每处访问都要有条目放行；没有访问对应的条目是过期条目，必须删除（按期删除不需要确认）；已到期的条目必须已经删除。</summary>
    public static void CheckEntries(string kind, IReadOnlyList<Entry> entries, IReadOnlyList<Access> accesses, string? milestone, List<string> failures)
    {
        foreach (var access in accesses.Where(a => !entries.Any(e => e.Covers(a))))
            failures.Add($"{kind}外的访问 [{access.Tag}] {access.Member} @ {access.File}:{access.Line}");
        foreach (var entry in entries.Where(e => !accesses.Any(e.Covers)))
            failures.Add($"{kind}条目已无对应访问，须删除：[{entry.Tag}] {entry.Member} @ {entry.Location}");
        foreach (var duplicate in entries.GroupBy(e => (e.Tag, e.Member, e.Location)).Where(g => g.Count() > 1))
            failures.Add($"{kind}条目重复：[{duplicate.Key.Tag}] {duplicate.Key.Member} @ {duplicate.Key.Location}");
        // 到期里程碑为 MSn；共享步骤体登记表的条目写“常设”
        foreach (var entry in entries.Where(e => string.IsNullOrWhiteSpace(e.Reason) || string.IsNullOrWhiteSpace(e.Package) || !e.Expiry.StartsWith("MS", StringComparison.Ordinal) && e.Expiry != "常设"))
            failures.Add($"{kind}条目缺少理由、工作包或到期里程碑：[{entry.Tag}] {entry.Member} @ {entry.Location}");
        if (milestone is not null)
            foreach (var entry in entries.Where(e => string.CompareOrdinal(e.Expiry, milestone) <= 0))
                failures.Add($"{kind}条目已于 {entry.Expiry} 到期：[{entry.Tag}] {entry.Member} @ {entry.Location}");
    }

    /// <summary>V2 建立初值时各约束标签对应的工作包与到期里程碑（主文 3.2）。</summary>
    public static (string Package, string Expiry) Schedule(Access access) => access.Tag switch
    {
        "I1b" => ("M1", "MS3"),
        "I2a" => ("K1", "MS1"),
        "I2b" => ("M3", "MS3"),
        "I2c" => ("M5", "MS3"),
        // I3a：MarkRuntime 的直接调用改经 Maintain.Rerun（K1）；I3b：“检查吸收”借用下降规则 CopyStructValue（O6）；其余由 K2 登记为共享步骤体
        "I3" => access.Member.EndsWith(".MarkRuntime", StringComparison.Ordinal) ? ("K1", "MS1")
            : access.Member.EndsWith(".CopyStructValue", StringComparison.Ordinal) ? ("O6", "MS2") : ("K2", "MS1"),
        "I4" => ("O2", "MS2"),
        "I7a" => ("K2", "MS1"),
        "I7b" => ("M6", "MS3"),
        "I10" => ("O8", "MS2"),
        _ => throw new InvalidOperationException($"未知约束标签 {access.Tag}"),
    };

    public static bool IsExemption(string tag) => tag is "I1b" or "I7a" or "I7b";

    // ---------- 族归属快照 ----------

    public static SortedDictionary<string, string> CurrentFamilies(SourceModel model) => new(model["Core"].Trees
        .Select(model.Relative).ToDictionary(f => f, SourceModel.Scope), StringComparer.Ordinal);

    public static SortedDictionary<string, string> ReadPairs(string path) => new(File.ReadLines(path).Where(l => l.Length > 0 && !l.StartsWith('#'))
        .Select(l => l.Split('\t')).ToDictionary(f => f[0], f => f[1]), StringComparer.Ordinal);

    public static void WritePairs(string path, string header, IReadOnlyDictionary<string, string> pairs) =>
        File.WriteAllLines(path, new[] { header }.Concat(pairs.OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => $"{p.Key}\t{p.Value}")));

    public static void CheckPairs(string name, IReadOnlyDictionary<string, string> recorded, IReadOnlyDictionary<string, string> current, List<string> failures)
    {
        foreach (var key in recorded.Keys.Union(current.Keys).Order(StringComparer.Ordinal))
        {
            var (was, now) = (recorded.GetValueOrDefault(key), current.GetValueOrDefault(key));
            if (was != now) failures.Add($"{name}与代码不一致 {key}：{was ?? "（无）"} → {now ?? "（无）"}（核对后用 architecture <repo> --write-snapshots 更新，并在提交说明中列出差异）");
        }
    }

    // ---------- 注册表快照 ----------

    private static readonly string[] Kinds =
    [
        "AnalysisAttribute", "MachinePassAttribute", "StatementRuleAttribute", "DefineRuleAttribute", "StoreRuleAttribute", "StoreTargetRuleAttribute",
        "CallRuleAttribute", "InvocationRuleAttribute", "InvocationOutputRuleAttribute", "ArgumentRuleAttribute", "ResultRuleAttribute",
        "ParameterBindingAttribute", "BodyProofAttribute",
    ];

    public sealed record Registration(string Kind, string Category, string Name, int Order, string After, string Invalidates, string Method);

    /// <summary>读取已构建的 Core 程序集中的注册方法。Analyze 的分析步骤与改写步骤共用一个排序类别，其余按种类各自排序。</summary>
    public static List<Registration> Registry()
    {
        var assembly = typeof(Cpp2CS.Recovery.MethodRecovery).Assembly;
        const BindingFlags members = BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
        var result = new List<Registration>();
        foreach (var method in assembly.GetTypes().SelectMany(t => t.GetMethods(members)))
            foreach (var attribute in method.GetCustomAttributes().Where(a => Kinds.Contains(a.GetType().Name)))
            {
                var type = attribute.GetType();
                var kind = type.Name[..^"Attribute".Length];
                var name = type.GetProperty("Name")?.GetValue(attribute) as string ?? method.Name;
                var order = (int)type.GetProperty("Order")!.GetValue(attribute)!;
                var after = type.GetProperty("After")?.GetValue(attribute) is string[] list ? string.Join(",", list) : "";
                var invalidates = type.GetProperty("Invalidates")?.GetValue(attribute)?.ToString() ?? "";
                var category = kind is "Analysis" or "MachinePass" ? "Analyze" : kind;
                result.Add(new(kind, category, name, order, after, invalidates, $"{method.DeclaringType!.Name}.{method.Name}"));
            }
        return result.OrderBy(r => r.Category, StringComparer.Ordinal).ThenBy(r => r.Order).ThenBy(r => r.Name, StringComparer.Ordinal).ToList();
    }

    public static IEnumerable<string> RegistryLines(IEnumerable<Registration> registry) => new[] { "# 种类\t名称\tOrder\tAfter\tInvalidates\t声明类型.方法" }
        .Concat(registry.Select(r => $"{r.Kind}\t{r.Name}\t{r.Order}\t{r.After}\t{r.Invalidates}\t{r.Method}"));

    /// <summary>同一排序类别内 Order 重复的组（I7a）：按名字决定顺序，K2 之前以豁免清单登记。</summary>
    public static IEnumerable<Access> DuplicateOrders(IEnumerable<Registration> registry) => registry.GroupBy(r => (r.Category, r.Order))
        .Where(g => g.Count() > 1).Select(g => new Access("I7a", $"{g.Key.Category}/Order={g.Key.Order}：{string.Join("、", g.Select(r => r.Name))}", "registry", 0));

    /// <summary>PassList.Run 的步骤名重复：L2 内部（I7b）、Prepare 内部与 Prepare 和 L2 之间（I7a）。</summary>
    public static IEnumerable<Access> DuplicatePasses(IEnumerable<(string Name, string Scope, string File, int Line)> passes)
    {
        foreach (var group in passes.GroupBy(p => p.Name).Where(g => g.Count() > 1))
        {
            var idioms = group.Count(p => p.Scope == "Idioms");
            var tag = idioms == group.Count() ? "I7b" : "I7a";
            yield return new Access(tag, $"{(tag == "I7b" ? "L2" : "Prepare")}/{group.Key}×{group.Count()}", "passes", 0);
        }
    }

    // ---------- 洞编码清单 ----------

    public static SortedDictionary<string, string> HoleCodes(IEnumerable<(string Rule, string File, string Method)> literals) => new(literals.GroupBy(l => l.Rule)
        .ToDictionary(g => g.Key, g => $"{g.Count()}\t{string.Join(",", g.Select(l => SourceModel.Scope(l.File)).Distinct().Order(StringComparer.Ordinal))}\t{g.Count(l => l.Method != g.Key)}"),
        StringComparer.Ordinal);
}
