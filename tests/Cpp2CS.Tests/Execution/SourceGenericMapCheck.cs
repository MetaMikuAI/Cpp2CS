using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

internal static class SourceGenericMapCheck
{
    [Command("source-generic-map", "实际生成的泛型回调源码在 CLR 中验证引用、标量和结构值", Arguments = "<生成的 C# 文件> <方法名>")]
    public static int Run(string sourceFile, string methodName)
    {
        var source = CSharpSyntaxTree.ParseText(File.ReadAllText(sourceFile));
        var method = source.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>().Single(m => m.Identifier.ValueText == methodName
            && m.TypeParameterList?.Parameters.Count == 2 && m.ParameterList.Parameters.Count == 2
            && m.ReturnType.ToString() == m.TypeParameterList.Parameters[1].Identifier.ValueText);
        var unit = SyntaxFactory.CompilationUnit().AddUsings(SyntaxFactory.UsingDirective(SyntaxFactory.ParseName("System")))
            .AddMembers(SyntaxFactory.ClassDeclaration("GeneratedMap").AddModifiers(SyntaxFactory.Token(SyntaxKind.PublicKeyword),
                SyntaxFactory.Token(SyntaxKind.StaticKeyword)).AddMembers(method));
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("GeneratedMap", [CSharpSyntaxTree.Create(unit)], references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release));
        using var stream = new MemoryStream();
        var result = compilation.Emit(stream);
        if (!result.Success) throw new InvalidOperationException(string.Join('\n', result.Diagnostics));
        var generic = Assembly.Load(stream.ToArray()).GetType("GeneratedMap")!.GetMethod(methodName)!;
        var a = new Assertions();
        void Check<T, U>(T input, U expected)
        {
            var invoke = generic.MakeGenericMethod(typeof(T), typeof(U)).CreateDelegate<Func<Func<T, U>?, T, U>>();
            a.True(EqualityComparer<U>.Default.Equals(default, invoke(null, input)), $"{typeof(T)} → {typeof(U)}：空回调返回默认值");
            var calls = 0;
            var actual = invoke(value => { calls++; a.True(EqualityComparer<T>.Default.Equals(input, value), "回调参数完整保留"); return expected; }, input);
            a.True(EqualityComparer<U>.Default.Equals(expected, actual), "返回值完整保留");
            a.Equal(1, calls, "回调只调用一次");
            if (!typeof(U).IsValueType) a.True(ReferenceEquals(expected, actual), "引用返回保留对象身份");
        }
        Check(int.MinValue, long.MaxValue);
        Check("input", new object());
        Check((object?)null, 17.25m);
        Check((byte)255, "output");
        Check(-0.25, (long.MinValue, "payload", decimal.MaxValue));
        Check((42, new object(), 1.5m), DayOfWeek.Friday);
        Check(DayOfWeek.Wednesday, (string?)null);
        Check(true, (false, -12.5, 123UL));
        return a.Finish("source-generic-map（仅源码 CLR，不替代原生对照）");
    }
}
