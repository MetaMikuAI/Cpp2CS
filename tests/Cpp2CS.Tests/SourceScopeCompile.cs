using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests;

internal static class SourceScopeCompile
{
    [Command("source-scope-compile", "只编译指定类型的已有源码并记录诊断，不重新反编译全程序集", Arguments = "<inventory> <recover> <output>")]
    public static int Run(string inventory, string directory, string output)
    {
        Directory.CreateDirectory(output);
        var files = ScopeSource.Read(inventory, directory);
        var errors = files.GroupBy(p => p.Assembly).SelectMany(group =>
        {
            var trees = group.Select(p => CSharpSyntaxTree.ParseText(File.ReadAllText(p.Path), new CSharpParseOptions(LanguageVersion.Preview), path: p.Name + ".cs")).ToArray();
            // 项目布局把不同泛型元数的同名类型合并到一个文件；以实际声明确定引用替换范围。
            var roots = trees.SelectMany(tree => tree.GetRoot().DescendantNodes().OfType<MemberDeclarationSyntax>())
                .Where(node => node is BaseTypeDeclarationSyntax or DelegateDeclarationSyntax
                    && !node.Ancestors().Any(parent => parent is BaseTypeDeclarationSyntax))
                .Select(node =>
                {
                    var name = node is BaseTypeDeclarationSyntax type ? type.Identifier.ValueText : ((DelegateDeclarationSyntax)node).Identifier.ValueText;
                    var arity = node is TypeDeclarationSyntax generic ? generic.TypeParameterList?.Parameters.Count ?? 0
                        : node is DelegateDeclarationSyntax callback ? callback.TypeParameterList?.Parameters.Count ?? 0 : 0;
                    if (arity > 0) name += "`" + arity;
                    var space = string.Join(".", node.Ancestors().OfType<BaseNamespaceDeclarationSyntax>().Reverse().Select(n => n.Name.ToString()));
                    return space.Length == 0 ? name : space + "." + name;
                }).ToHashSet();
            var sourceName = group.Key + ".Recovered";
            var assemblies = Path.Combine(directory, "assemblies-src");
            var references = ScopeCompilationReferences.Create(assemblies, group.Key, roots, sourceName, output,
                Execution.SourceAsyncCheck.CompilationReferences(assemblies, output, includeVoidBuilder: true));
            var compilation = CSharpCompilation.Create(sourceName, trees, references,
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
            var path = Path.Combine(output, sourceName + ".dll");
            var result = compilation.Emit(path);
            if (result.Success) Execution.SourceAsyncCheck.CheckCompiledAwait(path, trees.Sum(t =>
                t.GetRoot().DescendantNodes().OfType<AwaitExpressionSyntax>().Count()
                + t.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>().Count(i =>
                    i.Expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "AwaitUnsafeOnCompleted" })));
            return result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error);
        }).ToArray();
        File.WriteAllLines(Path.Combine(output, "errors.tsv"), new[] { "code\tfile\tmember\tline\tmessage" }.Concat(errors.Select(d =>
        {
            var tree = d.Location.SourceTree;
            var node = tree?.GetRoot().FindNode(d.Location.SourceSpan);
            var member = node?.AncestorsAndSelf().OfType<MemberDeclarationSyntax>().FirstOrDefault(m => m is MethodDeclarationSyntax or ConstructorDeclarationSyntax);
            var name = member switch
            {
                MethodDeclarationSyntax method => method.Identifier.ValueText + method.ParameterList,
                ConstructorDeclarationSyntax ctor => ctor.Identifier.ValueText + ctor.ParameterList,
                _ => "",
            };
            return $"{d.Id}\t{tree?.FilePath}\t{name}\t{d.Location.GetLineSpan().StartLinePosition.Line + 1}\t{d.GetMessage().Replace('\n', ' ').Replace('\r', ' ')}";
        })));
        var counts = errors.GroupBy(d => d.Id).OrderByDescending(g => g.Count()).Select(g => $"{g.Key}\t{g.Count()}").ToArray();
        File.WriteAllLines(Path.Combine(output, "summary.tsv"), new[] { "code\tcount" }.Concat(counts));
        Console.WriteLine($"源码文件 {files.Length}，错误 {errors.Length}；包括裁剪元数据、访问权限及已有缺口，不作为全类型编译通过。");
        Console.WriteLine(string.Join('\n', counts));
        return 0;
    }
}
