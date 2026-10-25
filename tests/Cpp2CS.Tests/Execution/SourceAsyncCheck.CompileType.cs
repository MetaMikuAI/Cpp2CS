using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

internal static partial class SourceAsyncCheck
{
    [Command("source-type-compile", "按匹配元数据编译实际导出的完整类型", Arguments = "<recover directory> <完整类型名>")]
    public static int CompileType(string directory, string type)
    {
        var proof = Path.Combine(directory, "type-compile", type);
        Directory.CreateDirectory(proof);
        var source = File.ReadAllText(Path.Combine(directory, "src", "Assembly-CSharp.dll_" + type + ".cs"));
        var tree = CSharpSyntaxTree.ParseText(source);
        var compilation = CSharpCompilation.Create("RecoveredType", [tree],
            CompilationReferences(Path.Combine(directory, "assemblies"), proof, includeVoidBuilder: true),
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
