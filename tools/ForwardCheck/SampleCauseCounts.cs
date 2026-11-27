using System.Text.RegularExpressions;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>逐方法保留独立洞的次数和原文。派生洞只参与“全部洞均在前五”的核算。</summary>
internal sealed class SampleCauseCounts
{
    public sealed record Example(string Text, ulong Address);
    public sealed class Bucket
    {
        public int Count { get; set; }
        public List<Example> Examples { get; set; } = [];
        public Dictionary<string, int> Uses { get; set; } = [];
    }

    public Dictionary<string, Bucket> Independent { get; set; } = [];
    public HashSet<string> All { get; set; } = [];
    public long VariantInterfaceRejections { get; set; }
    public long ArrayInterfaceRejections { get; set; }

    public void Add(string key, string text, ulong address, bool derived = false, IEnumerable<string>? uses = null)
    {
        All.Add(key);
        if (derived) return;
        if (!Independent.TryGetValue(key, out var bucket)) Independent.Add(key, bucket = new());
        bucket.Count++;
        if (bucket.Examples.Count < 3) bucket.Examples.Add(new(text, address));
        if (uses != null)
            foreach (string use in uses) bucket.Uses[use] = bucket.Uses.GetValueOrDefault(use) + 1;
    }

    // 项的具体表达式、实体编号和块号是诊断实参。16 字节等 ABI 规格常量保留。
    public static string Pattern(string layer, string what, string reason)
    {
        foreach (string prefix in new[] { "值不可得：", "调用的目标没有命名：", "地址由栈指针算出，但不是常量偏移：",
            "元数据事实不足：运行时类型表缺少 ", "元数据事实不足：开放类型 " })
            if (reason.StartsWith(prefix, StringComparison.Ordinal))
            {
                reason = prefix.TrimEnd('：', ' ') + "（…）";
                break;
            }
        string text = layer == "事实层" || what.Length == 0 ? reason : what + "：" + reason;
        text = Regex.Replace(text, @"0x[\da-fA-F]+|(?<=B)\d+|(?<=#)-?\d+|(?<=参)\d+|(?<=@)\d+|(?<=\.)\d+|(?<=出口)\d+|(?<=Integer)\d+|(?<=Vector)\d+|(?<=Preserved)\d+|(?<=Opaque)\d+", "N");
        text = Regex.Replace(text, @"(?<![A-Za-z\d])-?\d+(?![\d]| 字节)", "N");
        return (layer == "事实层" ? "事实" : "其余/" + layer) + " · " + text;
    }

    public static void Report(IEnumerable<(Sample.Item Item, SampleCauseCounts Counts)> measurements)
    {
        var methods = measurements.ToArray();
        var ranked = methods.SelectMany(m => m.Counts.Independent.Select(pair => (m.Item, pair.Key, Bucket: pair.Value)))
            .GroupBy(row => row.Key).Select(g => (Key: g.Key, Count: g.Sum(r => r.Bucket.Count), Rows: g.ToArray()))
            .OrderByDescending(g => g.Count).ThenBy(g => g.Key, StringComparer.Ordinal).ToArray();
        var top = ranked.Take(5).Select(g => g.Key).ToHashSet();
        Console.WriteLine($"根因合计\t{ranked.Sum(g => g.Count)}\t{methods.Count(m => m.Counts.Independent.Count != 0)}");
        foreach (var g in ranked)
        {
            Console.WriteLine($"根因\t{g.Key}\t{g.Count}\t{g.Rows.Length}");
            // 优先展示不同方法，其次展示同一方法的其他出现。
            var examples = g.Rows.SelectMany(r => r.Bucket.Examples.Select((e, i) => (r.Item, Example: e, Index: i)))
                .OrderBy(e => e.Index).Take(3);
            foreach (var e in examples)
                Console.WriteLine($"例\t{e.Item}\t{(e.Example.Address == 0 ? "无现场地址" : $"0x{e.Example.Address:x}")}\t{e.Example.Text}");
            foreach (var use in g.Rows.SelectMany(r => r.Bucket.Uses).GroupBy(u => u.Key)
                .Select(u => (u.Key, Count: u.Sum(x => x.Value))).OrderByDescending(u => u.Count).ThenBy(u => u.Key, StringComparer.Ordinal))
                Console.WriteLine($"读取用途\t{use.Key}\t{use.Count}");
        }
        foreach (var g in ranked.Where(g => g.Key.StartsWith("未命名调用 · 0x", StringComparison.Ordinal)).Take(20))
            Console.WriteLine($"调用目标前二十\t{g.Key.Split(' ')[^1]}\t{g.Count}\t{g.Rows.Length}");
        foreach (var g in ranked.Where(g => g.Key.StartsWith("其余/", StringComparison.Ordinal)).Take(20))
            Console.WriteLine($"其余模式前二十\t{g.Key}\t{g.Count}\t{g.Rows.Length}");
        Console.WriteLine($"前五覆盖全部独立洞的方法\t{methods.Count(m => m.Counts.Independent.Count != 0 && m.Counts.Independent.Keys.All(top.Contains))}");
        Console.WriteLine($"前五覆盖首洞及其余全部洞的方法\t{methods.Count(m => m.Counts.Independent.Count != 0 && m.Counts.All.IsSubsetOf(top))}");
    }
}
