using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

internal static partial class SourceAsyncCheck
{
    [Command("source-files-compile", "一起编译范围内的实际 C# 文件", Arguments = "<recover directory>")]
    public static int CompileScope(string directory)
    {
        var proof = Path.Combine(directory, "source-compile");
        Directory.CreateDirectory(proof);
        var trees = Directory.EnumerateFiles(Path.Combine(directory, "src"), "*.cs", SearchOption.AllDirectories)
            .Order().Select(path => CSharpSyntaxTree.ParseText(File.ReadAllText(path), path: path)).ToArray();
        var compilation = CSharpCompilation.Create("RecoveredScope", trees,
            CompilationReferences(Path.Combine(directory, "assemblies"), proof, includeVoidBuilder: true),
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        var result = compilation.Emit(Path.Combine(proof, "Recovered.dll"));
        File.WriteAllLines(Path.Combine(proof, "compile.txt"), result.Diagnostics.Select(d => d.ToString()));
        var a = new Assertions();
        a.True(result.Success, $"{trees.Length} 个实际 C# 文件编译，错误 {result.Diagnostics.Count(d => d.Severity == DiagnosticSeverity.Error)}；诊断：{proof}");
        return a.Finish("source-files-compile");
    }

    [Command("source-type-compile", "按匹配元数据编译实际导出的完整类型", Arguments = "<recover directory> <完整类型名>")]
    public static int CompileType(string directory, string type)
    {
        var proof = Path.Combine(directory, "type-compile", type);
        Directory.CreateDirectory(proof);
        var path = Path.Combine(directory, "src", "Assembly-CSharp.dll_" + type + ".cs");
        if (!File.Exists(path)) path = Path.Combine(directory, "src", "Assembly-CSharp.dll", type[..type.LastIndexOf('.')], type[(type.LastIndexOf('.') + 1)..] + ".cs");
        var source = File.ReadAllText(path);
        var tree = CSharpSyntaxTree.ParseText(source);
        var assembly = Path.GetFileName(path).Contains(".dll_", StringComparison.Ordinal)
            ? Path.GetFileName(path).Split(".dll_", 2, StringSplitOptions.None)[0] : Directory.GetParent(path)!.Parent!.Name[..^4];
        var sourceName = assembly + ".Recovered";
        var assemblies = Path.Combine(directory, "assemblies-src");
        var compilation = CSharpCompilation.Create(sourceName, [tree],
            ScopeCompilationReferences.Create(assemblies, assembly, new HashSet<string> { type }, sourceName, proof,
                CompilationReferences(assemblies, proof, includeVoidBuilder: true)),
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        var result = compilation.Emit(Path.Combine(proof, "Recovered.dll"));
        File.WriteAllLines(Path.Combine(proof, "compile.txt"), result.Diagnostics.Select(d => d.ToString()));
        var a = new Assertions();
        a.True(result.Success, type + " 实际完整类型编译：" + string.Join('\n', result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        if (result.Success) CheckCompiledAwait(Path.Combine(proof, "Recovered.dll"), tree.GetRoot().DescendantNodes().OfType<AwaitExpressionSyntax>().Count()
            + tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>().Count(i => i.Expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "AwaitUnsafeOnCompleted" }));
        return a.Finish("source-type-compile");
    }
}
