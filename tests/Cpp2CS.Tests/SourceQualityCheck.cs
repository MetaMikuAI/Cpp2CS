using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests;

internal static class SourceQualityCheck
{
    [Command("source-quality", "固定类型范围的源码残留、完整方法与原生字节覆盖率", Arguments = "<inventory> <recover> <output>")]
    public static int Run(string inventory, string directory, string output)
    {
        Directory.CreateDirectory(output);
        var rows = new List<object>();
        var totals = new Dictionary<string, int>();
        foreach (var source in ScopeSource.Read(inventory, directory))
        {
            var path = source.Path;
            var root = CSharpSyntaxTree.ParseText(File.ReadAllText(path)).GetRoot();
            var identifiers = root.DescendantTokens().Where(t => t.RawKind == (int)SyntaxKind.IdentifierToken).Select(t => t.ValueText).ToArray();
            var counts = new Dictionary<string, int>
            {
                ["escapedOpen"] = identifiers.Sum(s => s.Split("_003C", StringSplitOptions.None).Length - 1),
                ["escapedClose"] = identifiers.Sum(s => s.Split("_003E", StringSplitOptions.None).Length - 1),
                ["backingFieldReferences"] = identifiers.Count(s => s.Contains("BackingField", StringComparison.Ordinal)),
                ["displayClassDeclarations"] = root.DescendantNodes().OfType<ClassDeclarationSyntax>()
                    .Count(c => c.Identifier.ValueText.Contains("DisplayClass", StringComparison.Ordinal)),
                ["displayClassIdentifiers"] = identifiers.Count(s => s.Contains("DisplayClass", StringComparison.Ordinal)),
                ["unrecoveredCalls"] = root.DescendantNodes().OfType<InvocationExpressionSyntax>().Count(c => c.Expression is MemberAccessExpressionSyntax m
                    && m.Expression.ToString() is "Unrecovered" or "Cpp2CS.Unrecovered" or "global::Cpp2CS.Unrecovered"),
                ["visibleMoveNext"] = root.DescendantNodes().OfType<MethodDeclarationSyntax>().Count(m => m.Identifier.ValueText == "MoveNext"),
                ["moveNextCalls"] = root.DescendantNodes().OfType<InvocationExpressionSyntax>().Count(c => c.Expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "MoveNext" }
                    or IdentifierNameSyntax { Identifier.ValueText: "MoveNext" }),
                ["throwNull"] = root.DescendantNodes().Count(n => n is ThrowStatementSyntax { Expression.RawKind: (int)SyntaxKind.NullLiteralExpression }
                    or ThrowExpressionSyntax { Expression.RawKind: (int)SyntaxKind.NullLiteralExpression }),
                ["asyncMethods"] = root.DescendantNodes().OfType<MethodDeclarationSyntax>().Count(m => m.Modifiers.Any(t => t.RawKind == (int)SyntaxKind.AsyncKeyword)),
                ["iteratorMethods"] = root.DescendantNodes().OfType<MethodDeclarationSyntax>().Count(m => m.DescendantNodes().OfType<YieldStatementSyntax>().Any()),
            };
            foreach (var (key, value) in counts) totals[key] = totals.GetValueOrDefault(key) + value;
            rows.Add(new { type = source.Type, counts });
        }
        var records = File.ReadLines(Path.Combine(directory, "recovery.jsonl")).Select(l => JsonDocument.Parse(l)).ToArray();
        var targets = records.Select(d => d.RootElement).Where(r => !r.GetProperty("dependency").GetBoolean()).ToArray();
        var emitted = targets.Where(r => r.GetProperty("status").GetString() == "emitted").ToArray();
        var declarations = targets.Where(r => r.GetProperty("status").GetString() == "runtime-declaration").ToArray();
        var entries = File.ReadLines(Path.Combine(inventory, "native-entries.tsv")).Skip(1).Select(l => l.Split('\t'))
            .ToDictionary(p => p[0], p => long.Parse(p[1]));
        var recoveredEntries = emitted.Select(r => r.GetProperty("address").GetString()!).Distinct().ToArray();
        var bytes = recoveredEntries.Sum(e => entries[e]);
        var totalBytes = entries.Values.Sum();
        var summary = new
        {
            files = rows.Count, selectedMethods = targets.Length, emittedMethods = emitted.Length,
            holeMethods = targets.Count(r => r.GetProperty("status").GetString() == "hole"),
            emitFailedMethods = targets.Count(r => r.GetProperty("status").GetString() == "emit-failed"),
            runtimeDeclarationMethods = declarations.Length,
            runtimeDeclarationBytes = declarations.Select(r => r.GetProperty("address").GetString()!).Distinct().Sum(e => entries[e]),
            declarationsByKind = declarations.GroupBy(r => r.GetProperty("declaration").GetString()!).ToDictionary(g => g.Key,
                g => new { methods = g.Count(), bytes = g.Select(r => r.GetProperty("address").GetString()!).Distinct().Sum(e => entries[e]) }),
            source = totals, emittedBytes = bytes, totalBytes, byteCoverage = (double)bytes / totalBytes,
        };
        var options = new JsonSerializerOptions { WriteIndented = true };
        File.WriteAllText(Path.Combine(output, "summary.json"), JsonSerializer.Serialize(summary, options));
        File.WriteAllText(Path.Combine(output, "types.json"), JsonSerializer.Serialize(rows, options));
        Console.WriteLine(JsonSerializer.Serialize(summary, options));
        foreach (var record in records) record.Dispose();
        return 0;
    }
}
