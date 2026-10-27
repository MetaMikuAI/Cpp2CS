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
        var files = File.ReadLines(Path.Combine(inventory, "types.tsv")).Skip(1).Select(l => Path.Combine(directory, "src", l.Split('\t')[1])).ToArray();
        var errors = files.GroupBy(p => Path.GetFileName(p).Split(".dll_", 2, StringSplitOptions.None)[0]).SelectMany(group =>
        {
            var trees = group.Select(p => CSharpSyntaxTree.ParseText(File.ReadAllText(p), new CSharpParseOptions(LanguageVersion.Preview), path: Path.GetFileName(p))).ToArray();
            var roots = group.Select(p => Path.GetFileNameWithoutExtension(p)[(group.Key.Length + 5)..]).ToHashSet();
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
