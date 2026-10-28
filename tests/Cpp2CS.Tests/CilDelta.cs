using System.Text.Json;
using Mono.Cecil;

namespace Cpp2CS.Tests;

/// <summary>比较恢复产物的方法集合和 CIL；不要求附带 C# 文本，也不把新增方法视为回归。</summary>
internal static class CilDelta
{
    [Command("cil-delta", "比较两个恢复目录的新增、丢失及 CIL 变化，输出抽查清单", Arguments = "<before> <after> <output> [--source] [--partial] [--only 清单]")]
    public static int Run(string before, string after, string output, string[] options)
    {
        var assemblies = "assemblies";
        var partial = false;
        HashSet<string>? selected = null;
        for (var i = 0; i < options.Length; i++)
        {
            if (options[i] == "--source") assemblies = "assemblies-src";
            else if (options[i] == "--partial") partial = true;
            else if (options[i] == "--only" && i + 1 < options.Length)
                selected = File.ReadLines(options[++i]).Where(l => l.Length > 0 && !l.StartsWith('#')).ToHashSet(StringComparer.Ordinal);
            else throw new ArgumentException($"未知或不完整的参数：{options[i]}");
        }
        var old = partial ? ReadPartial(before, assemblies) : Read(before);
        var current = partial ? ReadPartial(after, assemblies) : Read(after);
        if (selected is not null)
        {
            old = old.Where(p => selected.Contains(p.Key)).ToDictionary();
            current = current.Where(p => selected.Contains(p.Key)).ToDictionary();
        }
        var added = current.Keys.Except(old.Keys).Order(StringComparer.Ordinal).ToArray();
        var lost = old.Keys.Except(current.Keys).Order(StringComparer.Ordinal).ToArray();
        var changed = new List<string>();
        var unchanged = 0;
        Directory.CreateDirectory(output);
        using var details = File.CreateText(Path.Combine(output, "cil-changes.txt"));
        foreach (var group in old.Keys.Intersect(current.Keys).GroupBy(k => old[k][0]))
        {
            using var left = ModuleDefinition.ReadModule(Path.Combine(before, assemblies, group.Key));
            using var right = ModuleDefinition.ReadModule(Path.Combine(after, assemblies, group.Key));
            foreach (var key in group)
            {
                if (old[key][0] != current[key][0]) throw new InvalidDataException($"{key} 的程序集改变");
                var previous = (MethodDefinition)left.LookupToken(Convert.ToInt32(old[key][5], 16));
                var next = (MethodDefinition)right.LookupToken(Convert.ToInt32(current[key][5], 16));
                if (EmittedBodyCheck.Describe(previous).AsSpan().SequenceEqual(EmittedBodyCheck.Describe(next)))
                {
                    unchanged++;
                    continue;
                }
                changed.Add(key);
                details.WriteLine($"== {key}");
                Dump(details, "before", previous);
                Dump(details, "after", next);
            }
        }
        File.WriteAllLines(Path.Combine(output, "added.tsv"), added);
        File.WriteAllLines(Path.Combine(output, "lost.tsv"), lost);
        File.WriteAllLines(Path.Combine(output, "changed.tsv"), changed.Order(StringComparer.Ordinal));
        var summary = JsonSerializer.Serialize(new
        {
            before = old.Count, after = current.Count, unchanged, changed = changed.Count,
            added = added.Length, lost = lost.Length,
            addedTargets = added.Count(k => current[k][^1] == "target"),
            changedTargets = changed.Count(k => current[k][^1] == "target"),
        }, new JsonSerializerOptions { WriteIndented = true });
        File.WriteAllText(Path.Combine(output, "cil-summary.json"), summary);
        Console.WriteLine(summary);
        var a = new Assertions();
        a.Equal(0, lost.Length, "原有写出方法没有丢失");
        return a.Finish("cil-delta");
    }

    private static Dictionary<string, string[]> Read(string directory) => File.ReadLines(Path.Combine(directory, "emitted.tsv"))
        .Select(line => line.Split('\t')).ToDictionary(row => $"{row[3]}\t{row[4]}", StringComparer.Ordinal);

    private static Dictionary<string, string[]> ReadPartial(string directory, string assemblies)
    {
        var result = new Dictionary<string, string[]>(StringComparer.Ordinal);
        foreach (var file in Directory.EnumerateFiles(Path.Combine(directory, assemblies), "*.dll").Order(StringComparer.Ordinal))
        {
            using var module = ModuleDefinition.ReadModule(file);
            foreach (var method in module.GetTypes().SelectMany(t => t.Methods).Where(m => m.HasBody
                && m.Body.Instructions.Any(i => i.Operand is MethodReference called && called.DeclaringType.FullName == "Cpp2CS.Unrecovered")))
                result.Add($"{module.Name}\t{method.FullName}",
                    [Path.GetFileName(file), "", "", "partial", method.FullName, $"0x{method.MetadataToken.ToUInt32():x8}", "target"]);
        }
        var expected = File.ReadLines(Path.Combine(directory, "recovery.jsonl")).Count(line =>
        {
            using var row = JsonDocument.Parse(line);
            return row.RootElement.GetProperty("partial").GetBoolean();
        });
        if (result.Count != expected) throw new InvalidDataException($"部分方法体清单为 {expected}，含缺口标记的方法体为 {result.Count}");
        return result;
    }

    private static void Dump(TextWriter writer, string label, MethodDefinition method)
    {
        writer.WriteLine($"-- {label}: {method.FullName}; InitLocals={method.Body.InitLocals}");
        foreach (var variable in method.Body.Variables) writer.WriteLine($"  local {variable.Index}: {variable.VariableType}");
        foreach (var instruction in method.Body.Instructions) writer.WriteLine($"  {instruction}");
        foreach (var handler in method.Body.ExceptionHandlers)
            writer.WriteLine($"  {handler.HandlerType}: try {handler.TryStart}..{handler.TryEnd}; handler {handler.HandlerStart}..{handler.HandlerEnd}; filter {handler.FilterStart}; catch {handler.CatchType}");
    }
}
