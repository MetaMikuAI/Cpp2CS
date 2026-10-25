using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>语言证据与执行证据分开记录；无原生代码的方法不冒充 verified。</summary>
public static class AutoPropertyManifest
{
    public static HashSet<string> ReadRejected(string? path) => path is null || !File.Exists(path) ? []
        : File.ReadLines(path).Where(l => l.Length > 0 && !l.StartsWith('#')).ToHashSet(StringComparer.Ordinal);

    public static void Write(string output, AccessorRecovery closure, string? rejectedPath)
    {
        File.WriteAllLines(Path.Combine(output, "autoprop-accessors.tsv"),
            new[] { "# F9b 语言定义：字段/访问器特性、属性关联、签名与静态性；原生验证另见 execution.tsv", "# address\tmethod\tfield\tbody\tnative\tavailable\toriginal-holes" }.Concat(
            closure.LanguageAccessors.OrderBy(p => p.Key.Index).Select(p =>
                $"0x{p.Key.Address:x}\t{p.Value.Method}\t{p.Value.Field}\t{(closure.Synthesized.ContainsKey(p.Key) ? "synthesized" : "recovered")}\t{(p.Key.Address == 0 ? "absent" : "present")}\t{closure.Candidates.ContainsKey(p.Key)}\t" +
                string.Join("；", closure.Synthesized.GetValueOrDefault(p.Key)?.Holes.Select(h => h.Reason) ?? []))));
        File.WriteAllLines(Path.Combine(output, "autoprop-rejected-input.tsv"), ReadRejected(rejectedPath).Order(StringComparer.Ordinal));
    }

    public static void RestoreSynthesized(string directory, ManagedTypes types, MethodRecoveryResult[] results)
    {
        var path = Path.Combine(directory, "autoprop-accessors.tsv");
        if (!File.Exists(path)) return;
        var wanted = File.ReadLines(path).Where(l => !l.StartsWith('#')).Select(l => l.Split('\t'))
            .Where(f => f[3] == "synthesized").Select(f => (Convert.ToUInt64(f[0], 16), f[1])).ToHashSet();
        var automatic = AutoPropertyAccessor.Candidates(types);
        for (var i = 0; i < results.Length; i++)
        {
            var result = results[i];
            if (!wanted.Contains((result.Entry, result.Method.ToString()))) continue;
            if (result.Body is not null || !automatic.TryGetValue(result.Method.Method, out var accessor))
                throw new InvalidDataException($"合成访问器的恢复状态或语言证据改变：{result.Method}");
            results[i] = result with { Body = AutoPropertyAccessor.Synthesize(accessor), Holes = [] };
        }
    }
}
