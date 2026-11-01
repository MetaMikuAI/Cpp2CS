using System.Text;
using Cpp2CS.Facts;
using Cpp2CS.Idioms;

namespace Cpp2CS.Cli;

/// <summary>L2 普查报告：idioms.txt（覆盖率、模板命中、残余与错误类别）与 idiom-residuals.tsv（全部类别及样例）。</summary>
internal static class IdiomReport
{
    public static string Write(ProgramFacts facts, IdiomCensus census, string output)
    {
        var text = new StringBuilder();
        var lifted = census.Functions - census.Failed;
        text.AppendLine($"L2 惯用法普查：{census.Functions} 个函数，{census.Elapsed.TotalSeconds:F0} s；" +
            $"失败 {census.Failed}；无残余 {census.Clean}（{Percent(census.Clean, census.Functions)}）");

        text.AppendLine().AppendLine("## helper 调用点（改写前 → 残余）");
        long total = 0, residual = 0;
        foreach (var (kind, count) in census.HelperCalls.OrderByDescending(p => p.Value))
        {
            var left = census.ResidualCalls(kind);
            total += count;
            residual += left;
            text.AppendLine($"  {kind,-22} {count,9} → {left,8}   消化 {Percent(count - left, count)}");
        }
        text.AppendLine($"  {"合计",-20} {total,9} → {residual,8}   消化 {Percent(total - residual, total)}");
        var indirectLeft = census.Residuals.Where(p => p.Key.StartsWith("indirect:")).Sum(p => p.Value.Count);
        text.AppendLine($"  {"间接调用",-18} {census.IndirectCalls,9} → {indirectLeft,8}   识别 {Percent(census.IndirectCalls - indirectLeft, census.IndirectCalls)}");

        text.AppendLine().AppendLine("## 模板命中");
        foreach (var (template, count) in census.Hits.OrderByDescending(p => p.Value)) text.AppendLine($"  {template,-24} {count,9}");

        // 守卫字节属于一个方法（s_Il2CppMethodInitialized）；内联把它连同守卫区域带进调用方，所以可以被多个函数使用，
        // 但各处初始化的槽位集合必须相同
        var guards = census.GuardOwners.Keys.ToHashSet();
        var referencing = new Dictionary<ulong, HashSet<int>>();
        foreach (var r in facts.Scan.All)
            if (guards.Contains(r.Target))
            {
                if (!referencing.TryGetValue(r.Target, out var set)) referencing[r.Target] = set = [];
                set.Add(facts.Code.IndexOf(r.Site));
            }
        var shared = census.GuardOwners.Where(p => p.Value.Count > 1).ToList();
        var foreign = referencing.Where(p => p.Value.Count > 1).ToList();
        var inconsistent = census.GuardSlotSets.Where(p => p.Value.Count > 1).ToList();
        text.AppendLine().AppendLine($"## 守卫字节：{guards.Count} 个；被多个函数当作守卫 {shared.Count}（内联）；被一个以上函数引用 {foreign.Count}；" +
            $"各处初始化的槽位集合不一致 {inconsistent.Count}");
        foreach (var (guard, sets) in inconsistent.Take(12))
            text.AppendLine($"  不一致 0x{guard:x}: {Clip(string.Join(" ‖ ", sets.Take(3)), 300)}");
        string Owner(ulong entry) => $"0x{entry:x} {facts.EntriesAt(entry).FirstOrDefault()?.Method?.ToString() ?? "?"}";
        foreach (var (guard, owners) in shared.OrderByDescending(p => p.Value.Count).Take(12))
            text.AppendLine($"  共用 0x{guard:x} ×{owners.Count}: {Clip(string.Join(" ‖ ", owners.Take(3).Select(Owner)), 300)}");
        foreach (var (guard, functions) in foreign.Where(p => census.GuardOwners[p.Key].Count == 1).OrderByDescending(p => p.Value.Count).Take(12))
            text.AppendLine($"  他处引用 0x{guard:x} ×{functions.Count}: 守卫于 {Owner(census.GuardOwners[guard][0])}；引用 {Clip(string.Join(" ‖ ", functions.Select(i => facts.Code.Functions[i].Start).Where(e => e != census.GuardOwners[guard][0]).Take(3).Select(Owner)), 300)}");

        text.AppendLine().AppendLine("## 残余类别（前 60）");
        foreach (var (category, tally) in census.Residuals.OrderByDescending(p => p.Value.Count).Take(60))
            text.AppendLine($"  {tally.Count,8}  {category}\n            {Clip(tally.Samples[0], 220)}");
        text.AppendLine().AppendLine("## 调用约定见证（不计入残余）");
        foreach (var (category, tally) in census.Abi.OrderByDescending(p => p.Value.Count))
            text.AppendLine($"  {tally.Count,8}  {category}\n            {Clip(tally.Samples[0], 220)}");
        text.AppendLine().AppendLine("## 错误类别");
        foreach (var (category, tally) in census.Errors.OrderByDescending(p => p.Value.Count))
            text.AppendLine($"  {tally.Count,8}  {Clip(category, 160)}\n            {Clip(tally.Samples[0], 220)}");

        File.WriteAllText(Path.Combine(output, "idioms.txt"), text.ToString());
        using var tsv = new StreamWriter(Path.Combine(output, "idiom-residuals.tsv"));
        tsv.WriteLine("kind\tcategory\tcount\tsamples");
        foreach (var (category, tally) in census.Residuals.OrderByDescending(p => p.Value.Count))
            tsv.WriteLine($"residual\t{category}\t{tally.Count}\t{string.Join(" ‖ ", tally.Samples).Replace('\t', ' ').Replace('\n', ' ')}");
        foreach (var (category, tally) in census.Abi.OrderByDescending(p => p.Value.Count))
            tsv.WriteLine($"abi\t{category}\t{tally.Count}\t{string.Join(" ‖ ", tally.Samples).Replace('\t', ' ').Replace('\n', ' ')}");
        foreach (var (category, tally) in census.Errors.OrderByDescending(p => p.Value.Count))
            tsv.WriteLine($"error\t{category}\t{tally.Count}\t{string.Join(" ‖ ", tally.Samples).Replace('\t', ' ').Replace('\n', ' ')}");
        using (var instances = new StreamWriter(Path.Combine(output, "template-instances.jsonl")))
            foreach (var (template, list) in census.Instances.OrderBy(p => p.Key))
                foreach (var instance in list)
                    instances.WriteLine(System.Text.Json.JsonSerializer.Serialize(new
                    {
                        template = template.ToString(),
                        function = instance.Function,
                        head = instance.Head,
                        exits = instance.Exits,
                        inputs = instance.Inputs,
                    }));
        return text.ToString();
    }

    private static string Percent(long part, long whole) => whole == 0 ? "—" : $"{100.0 * part / whole:F2}%";

    private static string Clip(string s, int n) => s.Length > n ? s[..n] + "…" : s;
}
