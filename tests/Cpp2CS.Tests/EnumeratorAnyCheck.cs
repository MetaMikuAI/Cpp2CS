using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class EnumeratorAnyCheck
{
    private sealed class Custom { public List<int>.Enumerator GetEnumerator() => new List<int>().GetEnumerator(); }

    [Command("enumerator-any", "单次枚举查询、标准库身份与空源异常", Gate = Gate.Unit)]
    public static int Run()
    {
        var compilation = new CSharpDecompiler(typeof(EnumeratorAnyCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        IdentifierExpression Id(string name) => new(name);
        InvocationExpression Call(string name) => new(new MemberReferenceExpression(Id("iterator"), name));
        var a = new Assertions();
        foreach (var mode in new[] { "list", "values", "custom", "extra-catch", "wrong-result", "current" })
        {
            var collection = compilation.FindType(mode == "values" ? typeof(Dictionary<int, int>.ValueCollection) : mode == "custom" ? typeof(Custom) : typeof(List<int>));
            Expression source = Id("values");
            if (mode == "values")
            {
                var dictionary = compilation.FindType(typeof(Dictionary<int, int>));
                source = new MemberReferenceExpression(Id("dictionary"), "Values");
                source.AddAnnotation(new MemberResolveResult(new ResolveResult(dictionary), dictionary.GetProperties().Single(p => p.Name == "Values")));
            }
            var get = collection.GetMethods().Single(m => m.Name == "GetEnumerator" && m.Parameters.Count == 0);
            var factory = new InvocationExpression(new MemberReferenceExpression(source, "GetEnumerator"));
            factory.AddAnnotation(new MemberResolveResult(new ResolveResult(collection), get));
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement { new ExpressionStatement(new AssignmentExpression(Id("result"),
                new ConditionalExpression(Call(mode == "current" ? "Current" : "MoveNext"), new PrimitiveExpression(mode == "wrong-result" ? 2UL : 1UL), new PrimitiveExpression(0UL)))) } };
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement
                { new ExpressionStatement(Call("Dispose")), new ThrowStatement(Id("error")) } };
            if (mode == "extra-catch") catcher.Body.Statements.InsertBefore(catcher.Body.Statements.First(), new ExpressionStatement(new InvocationExpression(Id("Log"))));
            guarded.CatchClauses.Add(catcher);
            var method = new MethodDeclaration { Name = "HasItem", ReturnType = new PrimitiveType("bool"), Body = new BlockStatement
            {
                new VariableDeclarationStatement(new SimpleType("Enumerator"), "iterator", new DefaultValueExpression(new SimpleType("Enumerator"))),
                new ExpressionStatement(new AssignmentExpression(Id("iterator"), factory)), new VariableDeclarationStatement(new PrimitiveType("ulong"), "result"),
                guarded, new ExpressionStatement(Call("Dispose")), new ReturnStatement(new BinaryOperatorExpression(new CastExpression(new PrimitiveType("byte"),
                    new BinaryOperatorExpression(new CastExpression(new PrimitiveType("int"), Id("result")), BinaryOperatorType.BitwiseAnd, new PrimitiveExpression(1))), BinaryOperatorType.InEquality, new PrimitiveExpression(0))),
            } };
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "Subject" }; type.Members.Add(method); tree.Members.Add(type);
            typeof(Decompilation).Assembly.GetType("Cpp2CS.Output.RecoveredForeach")!.GetMethod("RecoverAny", BindingFlags.NonPublic | BindingFlags.Static)!
                .Invoke(null, [tree, compilation]);
            var expected = mode is "list" or "values";
            a.Equal(expected ? 1 : 0, tree.Descendants.OfType<MemberReferenceExpression>().Count(m => m.MemberName == "Any"), $"{mode} 的库身份与清理边界");
            if (expected)
            {
                a.Equal(mode == "list" ? 1 : 0, tree.Descendants.OfType<ThrowExpression>().Count(), "可能为空的源保留 NullReferenceException");
                a.True(method.Body.Statements.ToArray() is [ReturnStatement], "返回值直接恢复为布尔查询");
            }
        }
        return a.Finish("enumerator-any");
    }
}
