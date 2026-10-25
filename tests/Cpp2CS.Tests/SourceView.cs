using Cpp2CS.Output;

namespace Cpp2CS.Tests;

internal static class SourceView
{
    [Command("source-view", "从已有源码程序集导出所选方法的所在类型，不重跑恢复", Arguments = "<recover 输出目录> <方法清单> <output>")]
    public static int Run(string directory, string methods, string output)
    {
        var selected = File.ReadLines(methods).Where(l => l.Length > 0 && !l.StartsWith('#')).ToHashSet(StringComparer.Ordinal);
        var rows = File.ReadLines(Path.Combine(directory, "emitted.tsv")).Select(l => l.Split('\t'))
            .Where(r => selected.Contains($"{r[3]}\t{r[4]}"));
        var assemblies = Path.Combine(directory, "assemblies-src");
        Directory.CreateDirectory(output);
        var invalid = Path.GetInvalidFileNameChars();
        var count = 0;
        foreach (var group in rows.GroupBy(r => r[0]))
        {
            var wanted = group.Select(r => (r[1], r[2])).ToHashSet();
            foreach (var source in Decompilation.Decompile(Path.Combine(assemblies, group.Key), assemblies,
                t => wanted.Contains((t.Namespace, t.Name)), false, recoveringBodies: true))
            {
                var name = new string((group.Key + "_" + source.TypeName).Select(c => invalid.Contains(c) ? '_' : c).ToArray());
                File.WriteAllText(Path.Combine(output, name + ".cs"), source.Source);
                count++;
            }
        }
        Console.WriteLine($"从已有 assemblies-src 导出 {count} 个类型；同类型的其他方法保持已有产物内容。");
        return 0;
    }
}
