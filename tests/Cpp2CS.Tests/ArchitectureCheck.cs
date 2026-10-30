using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests;

/// <summary>按实际符号引用检查模块边界，别名与完整类型名适用相同规则。</summary>
internal static class ArchitectureCheck
{
    [Command("architecture", "检查核心、写出与扩展的依赖方向", Arguments = "<repository>")]
    public static int Run(string repository)
    {
        var failures = new SortedSet<string>(StringComparer.Ordinal);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Concat(Directory.GetFiles(AppContext.BaseDirectory, "*.dll")).Distinct(StringComparer.OrdinalIgnoreCase)
            .Select(p => MetadataReference.CreateFromFile(p)).ToArray();
        foreach (var project in new[] { "Core", "Output", "Extensions", "Input", "Pipeline" })
        {
            var folder = Path.Combine(repository, "src", "Cpp2CS." + project);
            var trees = Directory.EnumerateFiles(folder, "*.cs", SearchOption.AllDirectories)
                .Where(p => !Path.GetRelativePath(folder, p).Split(Path.DirectorySeparatorChar).Any(s => s is "obj" or "bin"))
                .Select(p => CSharpSyntaxTree.ParseText(File.ReadAllText(p), new(LanguageVersion.Preview), p)).ToArray();
            var globals = CSharpSyntaxTree.ParseText("global using System; global using System.IO; global using System.Linq; global using System.Collections.Generic; global using System.Threading; global using System.Threading.Tasks;", new(LanguageVersion.Preview));
            var compilation = CSharpCompilation.Create("Cpp2CS." + project, trees.Append(globals),
                references.Where(r => Path.GetFileName(r.FilePath) != "Cpp2CS." + project + ".dll"), new(OutputKind.DynamicallyLinkedLibrary));
            foreach (var tree in trees)
            {
                var semantic = compilation.GetSemanticModel(tree);
                var root = tree.GetRoot();
                var source = root.DescendantNodes().OfType<BaseNamespaceDeclarationSyntax>().FirstOrDefault()?.Name.ToString() ?? "";
                foreach (var name in root.DescendantNodes().OfType<SimpleNameSyntax>().Where(n => !n.Ancestors().Any(a => a is UsingDirectiveSyntax)))
                {
                    var symbol = semantic.GetSymbolInfo(name).Symbol;
                    var target = symbol?.ContainingNamespace?.ToDisplayString() ?? "";
                    if (!Forbidden(source, target)) continue;
                    failures.Add($"{Path.GetRelativePath(repository, tree.FilePath)}:{name.GetLocation().GetLineSpan().StartLinePosition.Line + 1}: {source} → {target} ({symbol!.Name})");
                }
            }
        }
        foreach (var failure in failures) Console.WriteLine(failure);
        Console.WriteLine($"architecture: {failures.Count} 个越层引用");
        return failures.Count == 0 ? 0 : 1;
    }

    private static bool Within(string name, string layer) => name == "Cpp2CS." + layer || name.StartsWith("Cpp2CS." + layer + ".", StringComparison.Ordinal);
    private static bool Forbidden(string source, string target)
    {
        if (!target.StartsWith("Cpp2CS.", StringComparison.Ordinal)) return false;
        if (Within(source, "Facts.Derived") && new[] { "Managed", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Facts") && !Within(source, "Facts.Derived") && new[] { "Machine", "Idioms", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Machine") && new[] { "Idioms", "Managed", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Idioms") && new[] { "Managed", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Managed") && new[] { "Machine", "Idioms", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Model") && new[] { "Facts", "Machine", "Managed", "Recovery", "Idioms" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Output") && new[] { "Recovery", "Extensions", "Pipeline" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Extensions") && Within(target, "Pipeline")) return true;
        return !new[] { "Output", "Extensions", "Input", "Pipeline" }.Any(l => Within(source, l))
            && new[] { "Output", "Extensions", "Pipeline" }.Any(l => Within(target, l));
    }
}
