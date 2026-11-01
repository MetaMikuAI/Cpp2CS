using Cpp2CS.Tests.Architecture;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests;

/// <summary>
/// 架构检查：按实际符号引用检查层次依赖（别名、完整类型名、var 与目标类型的 new() 适用相同规则）；
/// 注册的步骤与规则的 Id 前缀等于所在族目录；方法会话只在内核中出现，规则经作用域访问它。
/// </summary>
internal static class ArchitectureCheck
{
    [Command("architecture", "检查层次依赖、注册 Id 与族目录一致、方法会话只在内核中使用", Arguments = "<repository> [--deps]")]
    public static int Run(string repository, string[] options)
    {
        var model = SourceModel.Load(repository);
        if (options.Contains("--deps")) return Dependencies(model);
        var failures = new List<string>();
        failures.AddRange(Layers(model));
        failures.AddRange(Registrations(model));
        failures.AddRange(SessionUses(model));
        foreach (var failure in failures) Console.WriteLine($"✗ {failure}");
        Console.WriteLine($"architecture：失败 {failures.Count} 项");
        return failures.Count == 0 ? 0 : 1;
    }

    /// <summary>注册方法（Step、Rule）的 Id 前缀须等于声明所在的族目录名（小写），例如 Recovery/Frames 中的 Id 以 frames. 开头。</summary>
    private static IEnumerable<string> Registrations(SourceModel model)
    {
        var core = model["Core"];
        foreach (var tree in core.Trees)
        {
            var file = model.Relative(tree);
            var parts = file.Split('/');
            var family = parts.Length > 4 && parts[2] == "Recovery" ? parts[3].ToLowerInvariant() : null;
            var semantic = core.Compilation.GetSemanticModel(tree);
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
            {
                if (semantic.GetDeclaredSymbol(declaration) is not { } method) continue;
                foreach (var attribute in method.GetAttributes().Where(a => a.AttributeClass?.Name is "StepAttribute" or "RuleAttribute"))
                {
                    var id = attribute.ConstructorArguments.Select(a => a.Value).OfType<string>().First();
                    var prefix = id[..Math.Max(0, id.IndexOf('.'))];
                    if (prefix != family)
                        yield return $"注册 Id {id} 的前缀与族目录不一致：{file}:{SourceModel.Line(declaration)}";
                }
            }
        }
    }

    /// <summary>方法会话类型只在 Recovery/Kernel 中出现；注册表与恢复入口（MethodRecovery）是内核的门面，同样允许。</summary>
    private static IEnumerable<string> SessionUses(SourceModel model)
    {
        string[] allowed = ["src/Cpp2CS.Core/Recovery/Kernel/", "src/Cpp2CS.Core/Recovery/Rules/RuleRegistry.cs", "src/Cpp2CS.Core/Recovery/MethodRecovery.cs"];
        var core = model["Core"];
        foreach (var tree in core.Trees)
        {
            var file = model.Relative(tree);
            if (allowed.Any(a => file.StartsWith(a, StringComparison.Ordinal))) continue;
            var semantic = core.Compilation.GetSemanticModel(tree);
            foreach (var name in tree.GetRoot().DescendantNodes().OfType<IdentifierNameSyntax>().Where(n => n.Identifier.Text == "MethodSession"))
                if (semantic.GetSymbolInfo(name).Symbol is INamedTypeSymbol { Name: "MethodSession" })
                    yield return $"规则代码引用了方法会话：{file}:{SourceModel.Line(name)}";
        }
    }
    /// <summary>命名空间依赖矩阵（诊断用）：源命名空间前两级 → 目标命名空间前两级，按引用次数。</summary>
    private static int Dependencies(SourceModel model)
    {
        var edges = new SortedDictionary<string, int>(StringComparer.Ordinal);
        foreach (var project in model.Projects.Where(p => p.Name != "Tests"))
            foreach (var (tree, source, target, _) in References(project))
            {
                static string Head(string ns) => string.Join('.', ns.Split('.').Take(2));
                if (Head(source) != Head(target)) edges[$"{Head(source)} → {Head(target)}"] = edges.GetValueOrDefault($"{Head(source)} → {Head(target)}") + 1;
            }
        foreach (var (edge, count) in edges) Console.WriteLine($"{count,6}  {edge}");
        return 0;
    }

    /// <summary>每个显式名称、var 声明与目标类型 new() 引用的类型或成员所在的命名空间。</summary>
    private static IEnumerable<(SyntaxTree Tree, string Source, string Target, (SyntaxNode Node, string Symbol) Site)> References(SourceModel.Project project)
    {
        foreach (var tree in project.Trees)
        {
            var semantic = project.Compilation.GetSemanticModel(tree);
            var root = tree.GetRoot();
            var source = root.DescendantNodes().OfType<BaseNamespaceDeclarationSyntax>().FirstOrDefault()?.Name.ToString() ?? "";
            foreach (var name in root.DescendantNodes().OfType<SimpleNameSyntax>().Where(n => !n.Ancestors().Any(a => a is UsingDirectiveSyntax)))
                if (semantic.GetSymbolInfo(name).Symbol is { } symbol)
                    yield return (tree, source, symbol.ContainingNamespace?.ToDisplayString() ?? "", (name, symbol.Name));
            foreach (var node in root.DescendantNodes().Where(n => n is ImplicitObjectCreationExpressionSyntax || n is VariableDeclarationSyntax { Type.IsVar: true }))
            {
                var type = node is VariableDeclarationSyntax declaration ? semantic.GetTypeInfo(declaration.Type).Type : semantic.GetTypeInfo(node).Type;
                if (type is not null) yield return (tree, source, type.ContainingNamespace?.ToDisplayString() ?? "", (node, type.Name));
            }
        }
    }

    private static List<string> Layers(SourceModel model)
    {
        var failures = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var project in model.Projects.Where(p => p.Name != "Tests"))
            foreach (var (tree, source, target, (node, symbol)) in References(project))
                if (Forbidden(source, target))
                    failures.Add($"越层引用 {model.Relative(tree)}:{SourceModel.Line(node)}: {source} → {target} ({symbol})");
        return failures.ToList();
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
        // 基础层：Image、Ir 只依赖 Model；Calls 只依赖 Ir、Managed、Model；Diagnostics 不依赖其他层；Options 只依赖 Diagnostics；Input 不依赖分析层
        if (Within(source, "Image") && new[] { "Ir", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls", "Diagnostics", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Ir") && new[] { "Image", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls", "Diagnostics", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Calls") && new[] { "Image", "Facts", "Machine", "Idioms", "Recovery", "Diagnostics", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Diagnostics") && new[] { "Image", "Model", "Ir", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Options") && new[] { "Image", "Model", "Ir", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Input") && new[] { "Machine", "Idioms", "Managed", "Recovery", "Calls" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Output") && new[] { "Recovery", "Extensions", "Pipeline" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Extensions") && Within(target, "Pipeline")) return true;
        return !new[] { "Output", "Extensions", "Input", "Pipeline", "Cli" }.Any(l => Within(source, l))
            && new[] { "Output", "Extensions", "Pipeline", "Cli" }.Any(l => Within(target, l));
    }
}
