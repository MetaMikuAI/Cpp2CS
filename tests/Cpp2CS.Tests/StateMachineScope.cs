using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests;

/// <summary>以元数据身份统计目标范围的状态机；源码折叠和底层 MoveNext 留存分别计数。</summary>
internal static partial class StateMachineScope
{
    private sealed record Machine(string Namespace, string Kind, string Entry, string Method, string Name,
        string Parameters, string StateMachine, string SourceFile, string MoveNext);
    private static string Hex(ulong value) => $"0x{value:x}";
    private static string Identifier(string value) => string.Concat(value.Split('`')[0].Select(c => char.IsLetterOrDigit(c) || c == '_' ? c.ToString() : $"_{(int)c:X4}"));

    [Command("state-machine-inventory", "指定命名空间的 async、迭代器及其他 MoveNext 清单", Arguments = "<binary> <metadata> <namespace> <output>")]
    public static int Inventory(string binary, string metadata, string prefix, string output)
    {
        if (string.IsNullOrWhiteSpace(prefix)) throw new ArgumentException("命名空间不能为空");
        var facts = FactsBuilder.Build(binary, metadata);
        return Inventory(facts.Model.Methods, t => t.Namespace == prefix || t.Namespace.StartsWith(prefix + ".", StringComparison.Ordinal) ? prefix : "", output, false);
    }

    private static int Inventory(IEnumerable<MethodDef> allMethods, Func<TypeDef, string> scope, string output, bool includeOrdinary)
    {
        Directory.CreateDirectory(output);
        var rows = new List<Machine>();
        var members = new HashSet<MethodDef>();
        var known = new HashSet<TypeDef>();
        var selected = allMethods.Where(m => scope(m.Owner).Length != 0).ToArray();
        if (includeOrdinary) members.UnionWith(selected);
        foreach (var method in selected)
        foreach (var attribute in method.CustomAttributes)
        {
            var kind = attribute.Constructor.Owner.FullName switch
            {
                "System.Runtime.CompilerServices.AsyncStateMachineAttribute" => "async",
                "System.Runtime.CompilerServices.IteratorStateMachineAttribute" => "iterator",
                _ => null,
            };
            if (kind is null || attribute.Arguments is not [{ Value: DefinitionRef machine }]) continue;
            var next = machine.Definition.Methods.Single(m => m.Name == "MoveNext");
            var top = method.Owner;
            while (top.DeclaringType is not null) top = top.DeclaringType;
            rows.Add(new(scope(method.Owner), kind, Hex(method.Address), method.ToString(), Identifier(method.Name),
                string.Join(';', method.Parameters.Select(p => Identifier(p.Name))), Identifier(machine.Definition.Name),
                top.Assembly + "_" + top.FullName + ".cs", Hex(next.Address)));
            known.Add(machine.Definition);
            members.Add(method);
            members.UnionWith(machine.Definition.Methods);
        }
        var others = selected.Where(m => m.Name == "MoveNext" && !known.Contains(m.Owner)).ToArray();
        File.WriteAllLines(Path.Combine(output, "other-movenext.tsv"), others.Select(m => $"{Hex(m.Address)}\t{m}\t{string.Join(';', m.Owner.Interfaces)}"));
        File.WriteAllText(Path.Combine(output, "inventory.json"), JsonSerializer.Serialize(rows, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllLines(Path.Combine(output, "methods.tsv"), members.Concat(others).Where(m => m.Address != 0).DistinctBy(m => m.Address)
            .OrderBy(m => m.Address).Select(m => $"{Hex(m.Address)}\t{m}"));
        foreach (var ns in selected.Select(m => scope(m.Owner)).Distinct())
            Console.WriteLine($"{ns}: async={rows.Count(r => r.Namespace == ns && r.Kind == "async")}; iterator={rows.Count(r => r.Namespace == ns && r.Kind == "iterator")}; otherMoveNext={others.Count(m => scope(m.Owner) == ns)}");
        Console.WriteLine($"范围方法={File.ReadLines(Path.Combine(output, "methods.tsv")).Count()}");
        return 0;
    }

    [Command("state-machine-report", "按实际源码统计 async/yield 折叠、残留和未写出入口", Arguments = "<inventory directory> <recover directory> <output>")]
    public static int Report(string inventoryDirectory, string recoverDirectory, string output)
    {
        Directory.CreateDirectory(output);
        var inventory = JsonSerializer.Deserialize<Machine[]>(File.ReadAllText(Path.Combine(inventoryDirectory, "inventory.json")))!;
        var lifting = File.ReadLines(Path.Combine(recoverDirectory, "async-lifting.tsv")).Skip(1).Select(l => l.Split('\t')).ToDictionary(p => p[0]);
        var recovery = File.ReadLines(Path.Combine(recoverDirectory, "recovery.jsonl")).Select(l => JsonDocument.Parse(l)).ToArray();
        var status = recovery.ToDictionary(d => d.RootElement.GetProperty("address").GetString()!, d => d.RootElement.GetProperty("status").GetString()!);
        var sources = inventory.Select(r => r.SourceFile).Distinct().ToDictionary(f => f, f =>
            File.Exists(Path.Combine(recoverDirectory, "src", f)) ? CSharpSyntaxTree.ParseText(File.ReadAllText(Path.Combine(recoverDirectory, "src", f))).GetRoot() : null);
        var rows = new List<string[]>();
        foreach (var machine in inventory)
        {
            var source = sources[machine.SourceFile];
            var nested = source?.DescendantNodes().OfType<TypeDeclarationSyntax>().Any(t => t.Identifier.ValueText == machine.StateMachine) == true;
            var candidates = source?.DescendantNodes().OfType<MethodDeclarationSyntax>().Where(m => m.Identifier.ValueText == machine.Name
                && string.Join(';', m.ParameterList.Parameters.Select(p => p.Identifier.ValueText)) == machine.Parameters).ToArray() ?? [];
            var folded = candidates.Length == 1 && (machine.Kind == "async" ? candidates[0].Modifiers.Any(SyntaxKind.AsyncKeyword)
                : candidates[0].DescendantNodes().OfType<YieldStatementSyntax>().Any());
            var state = folded ? "folded" : nested ? "residual" : "unavailable";
            var reason = machine.Kind == "async" && lifting.TryGetValue(machine.Entry, out var lift) ? lift[3]
                : $"入口:{status.GetValueOrDefault(machine.Entry, "no-entry")}; MoveNext:{status.GetValueOrDefault(machine.MoveNext, "no-entry")}";
            var holes = folded && (status.GetValueOrDefault(machine.Entry) != "emitted" || status.GetValueOrDefault(machine.MoveNext) != "emitted"
                || candidates[0].ToString().Contains("Unrecovered", StringComparison.Ordinal));
            rows.Add([machine.Namespace, machine.Kind, machine.Entry, machine.Method, machine.MoveNext, state, nested.ToString(), reason, holes.ToString()]);
        }
        File.WriteAllLines(Path.Combine(output, "states.tsv"), new[] { "namespace\tkind\tentry\tmethod\tmoveNext\tstatus\tvisibleMoveNextType\treason\tfoldedWithHoles" }.Concat(rows.Select(r => string.Join('\t', r))));
        var summary = new List<string> { "namespace\tkind\ttotal\tfolded\tresidual\tunavailable\tvisibleMoveNextTypes\tfoldedWithHoles" };
        foreach (var ns in inventory.Select(r => r.Namespace).Distinct())
        foreach (var kind in new[] { "async", "iterator" })
        {
            var selected = rows.Where(r => r[0] == ns && r[1] == kind).ToArray();
            summary.Add($"{ns}\t{kind}\t{selected.Length}\t{selected.Count(r => r[5] == "folded")}\t{selected.Count(r => r[5] == "residual")}\t{selected.Count(r => r[5] == "unavailable")}\t{selected.Count(r => r[6] == "True")}\t{selected.Count(r => r[8] == "True")}");
        }
        File.WriteAllLines(Path.Combine(output, "summary.tsv"), summary);
        Console.WriteLine(string.Join('\n', summary));
        foreach (var document in recovery) document.Dispose();
        if (File.Exists(Path.Combine(inventoryDirectory, "types.tsv"))) TypeReport(inventoryDirectory, recoverDirectory, output);
        else EscapedIdentifiers(recoverDirectory, output);
        return 0;
    }

    [Command("escaped-identifiers", "导出源码中 _003C、_003E 标识符出现次数", Arguments = "<recover directory> <output>")]
    public static int EscapedIdentifiers(string recoverDirectory, string output)
    {
        Directory.CreateDirectory(output);
        var files = new List<(string Namespace, string File, int Open, int Close, int References)>();
        foreach (var path in Directory.GetFiles(Path.Combine(recoverDirectory, "src"), "*.cs"))
        {
            var source = CSharpSyntaxTree.ParseText(File.ReadAllText(path)).GetRoot();
            var name = source.DescendantNodes().OfType<BaseNamespaceDeclarationSyntax>().FirstOrDefault()?.Name.ToString() ?? "";
            // 统计标识符的每次出现，排除字符串与注释；同一名称的重复引用仍计数。
            var identifiers = source.DescendantTokens().Where(t => t.IsKind(SyntaxKind.IdentifierToken)).Select(t => t.ValueText).ToArray();
            files.Add((name, Path.GetFileName(path), identifiers.Sum(s => s.Split("_003C", StringSplitOptions.None).Length - 1),
                identifiers.Sum(s => s.Split("_003E", StringSplitOptions.None).Length - 1),
                identifiers.Count(s => s.Contains("_003C", StringComparison.Ordinal) || s.Contains("_003E", StringComparison.Ordinal))));
        }
        File.WriteAllLines(Path.Combine(output, "escaped-identifiers-files.tsv"), new[] { "namespace\tfile\t_003C\t_003E\tescapedReferences" }
            .Concat(files.OrderBy(f => f.File, StringComparer.Ordinal).Select(f => $"{f.Namespace}\t{f.File}\t{f.Open}\t{f.Close}\t{f.References}")));
        var summary = new[] { "namespace\tfiles\t_003C\t_003E\tescapedReferences" }.Concat(files.Select(f => f.Namespace).Distinct().Order(StringComparer.Ordinal).Select(ns =>
        {
            var selected = files.Where(f => f.Namespace == ns).ToArray();
            return $"{ns}\t{selected.Length}\t{selected.Sum(f => f.Open)}\t{selected.Sum(f => f.Close)}\t{selected.Sum(f => f.References)}";
        })).ToArray();
        File.WriteAllLines(Path.Combine(output, "escaped-identifiers.tsv"), summary);
        Console.WriteLine(string.Join('\n', summary));
        return 0;
    }
}
