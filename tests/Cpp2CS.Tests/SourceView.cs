using Cpp2CS.Output;

namespace Cpp2CS.Tests;

internal static class SourceView
{
    [Command("type-source-view", "按类型清单导出已有源码程序集，包含无完整方法的类型", Arguments = "<inventory> <recover 输出目录> <output>")]
    public static int Types(string inventory, string directory, string output)
    {
        var requested = File.ReadLines(Path.Combine(inventory, "types.tsv")).Skip(1).Select(l => l.Split('\t')[1]).ToHashSet();
        var assemblies = Path.Combine(directory, "assemblies-src");
        Directory.CreateDirectory(output);
        var count = 0;
        foreach (var assembly in Directory.GetFiles(assemblies, "*.dll").Where(p => requested.Any(f => f.StartsWith(Path.GetFileName(p) + "_", StringComparison.Ordinal))))
            foreach (var source in Decompilation.Decompile(assembly, assemblies,
                t => requested.Contains(Path.GetFileName(assembly) + "_" + t.ReflectionName + ".cs"), false, recoveringBodies: true))
            {
                File.WriteAllText(Path.Combine(output, Path.GetFileName(assembly) + "_" + source.TypeName + ".cs"), source.Source);
                count++;
            }
        if (count != requested.Count) throw new InvalidDataException($"类型清单 {requested.Count}，实际导出 {count}");
        Console.WriteLine($"从已有 assemblies-src 导出 {count} 个类型。");
        return 0;
    }

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
