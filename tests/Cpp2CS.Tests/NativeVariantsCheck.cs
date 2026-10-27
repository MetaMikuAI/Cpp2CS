using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class NativeVariantsCheck
{
    [Command("native-variants", "固定方法清单之外的原生实例入口及互不覆盖的恢复清单", Arguments = "<binary> <metadata> <methods.tsv> <output>")]
    public static int Run(string binary, string metadata, string methodList, string output)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var selected = File.ReadLines(methodList).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t'))
            .Select(p => RecoveryTarget.Find(facts, Convert.ToUInt64(p[0], 16), p[1])).ToArray();
        var methods = selected.Select(t => t.Instance.Method).ToHashSet();
        var chosen = selected.Select(t => t.Entry).ToHashSet();
        var variants = facts.Model.Code.Where(p => !chosen.Contains(p.Key) && facts.Code.RegionOf(p.Key) == CodeRegion.Managed)
            .SelectMany(p => p.Value.Where(o => methods.Contains(o.Method.Method)).DistinctBy(o => o.Method.Method)
                .Select(o => new RecoveryTarget(o.Method, p.Key))).OrderBy(t => t.Entry).ToArray();
        Directory.CreateDirectory(output);
        File.WriteAllLines(Path.Combine(output, "variants.tsv"), new[] { "entry\tbytes\tmethod\tprimary\tdefinition" }.Concat(variants.Select(t =>
            $"0x{t.Entry:x}\t{facts.Code.At(t.Entry)!.Size}\t{t.Instance}\t0x{selected.Single(s => s.Instance.Method == t.Instance.Method).Entry:x}\t{t.Instance.Method.Index}")));
        var grouped = variants.GroupBy(t => t.Instance.Method).ToDictionary(g => g.Key, g => g.OrderBy(t => t.Entry).ToArray());
        var count = grouped.Values.Select(g => g.Length).DefaultIfEmpty(0).Max();
        for (var batch = 0; batch < count; batch++)
        {
            var targets = selected.Select(t => grouped.TryGetValue(t.Instance.Method, out var alternatives) && batch < alternatives.Length ? alternatives[batch] : t).ToArray();
            File.WriteAllLines(Path.Combine(output, $"methods-{batch:D2}.tsv"), targets.Select(t => $"0x{t.Entry:x}\t{t.Instance}"));
        }
        var unique = variants.Select(t => t.Entry).Distinct().ToArray();
        Console.WriteLine($"固定方法 {selected.Length}，所选入口 {chosen.Count}；其他入口 {unique.Length}，定义/入口对 {variants.Length}，涉及定义 {grouped.Count}");
        Console.WriteLine($"其他入口字节 {unique.Sum(e => (long)facts.Code.At(e)!.Size)}；恢复清单 {count} 份，每份保留完整固定范围，不以多个实例覆盖同一方法");
        foreach (var pair in grouped.OrderByDescending(p => p.Value.Sum(t => (long)facts.Code.At(t.Entry)!.Size)))
            Console.WriteLine($"{pair.Value.Length}\t{pair.Value.Sum(t => (long)facts.Code.At(t.Entry)!.Size)}\t{pair.Key}");
        return 0;
    }
}
