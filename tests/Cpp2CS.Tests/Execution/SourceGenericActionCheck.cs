using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

internal static class SourceGenericActionCheck
{
    [Command("source-generic-action", "实际四参数泛型回调源码的空回调、参数和调用次数", Arguments = "<生成的 C# 文件> <方法名>")]
    public static int Run(string sourceFile, string methodName)
    {
        var method = CSharpSyntaxTree.ParseText(File.ReadAllText(sourceFile)).GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>()
            .Single(m => m.Identifier.ValueText == methodName && m.TypeParameterList?.Parameters.Count == 4 && m.ParameterList.Parameters.Count == 5);
        var unit = SyntaxFactory.CompilationUnit().AddUsings(SyntaxFactory.UsingDirective(SyntaxFactory.ParseName("System")))
            .AddMembers(SyntaxFactory.ClassDeclaration("GeneratedAction").AddModifiers(SyntaxFactory.Token(SyntaxKind.PublicKeyword),
                SyntaxFactory.Token(SyntaxKind.StaticKeyword)).AddMembers(method));
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator).Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("GeneratedAction", [CSharpSyntaxTree.Create(unit)], references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release));
        using var stream = new MemoryStream();
        var result = compilation.Emit(stream);
        if (!result.Success) throw new InvalidOperationException(string.Join('\n', result.Diagnostics));
        var generic = Assembly.Load(stream.ToArray()).GetType("GeneratedAction")!.GetMethod(methodName)!;
        var assertions = new Assertions();
        void Check<A, B, C, D>(A first, B second, C third, D fourth)
        {
            var invoke = generic.MakeGenericMethod(typeof(A), typeof(B), typeof(C), typeof(D))
                .CreateDelegate<Action<Action<A, B, C, D>?, A, B, C, D>>();
            invoke(null, first, second, third, fourth);
            var calls = 0;
            invoke((a, b, c, d) =>
            {
                calls++;
                assertions.True(EqualityComparer<A>.Default.Equals(first, a), "第一参数完整保留");
                assertions.True(EqualityComparer<B>.Default.Equals(second, b), "第二参数完整保留");
                assertions.True(EqualityComparer<C>.Default.Equals(third, c), "第三参数完整保留");
                assertions.True(EqualityComparer<D>.Default.Equals(fourth, d), "第四参数完整保留");
            }, first, second, third, fourth);
            assertions.Equal(1, calls, "回调只执行一次");
        }
        Check(int.MinValue, "text", (long.MaxValue, new object(), 12.5m), -0.25);
        Check((object?)null, decimal.MaxValue, new object(), (false, 42, "value"));
        Check(true, DayOfWeek.Friday, (byte)255, (string?)null);
        return assertions.Finish("source-generic-action（仅源码 CLR，不替代原生对照）");
    }
}
