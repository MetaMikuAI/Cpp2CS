using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class SearchForeachCheck
{
    private sealed class Disposable : IDisposable { public void Dispose() { } }

    [Command("search-foreach", "查找枚举的耗尽、提前退出和结果使用边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var types = new CSharpDecompiler(typeof(SearchForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        var disposable = types.FindType(typeof(Disposable));
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Set(string name, Expression value) => new(new AssignmentExpression(Id(name), value));
        InvocationExpression Call(string member) => new(new MemberReferenceExpression(Id("iterator"), member));
        var a = new Assertions();
        foreach (var negate in new[] { false, true })
        foreach (var mode in new[] { "valid", "result-read", "enum-escape", "extra-entry", "element-write" })
        {
            var method = new MethodDeclaration { Name = "Find", ReturnType = new PrimitiveType("ulong"), Body = new BlockStatement() };
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "Subject" }; type.Members.Add(method); tree.Members.Add(type);
            var outer = method.Body;
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Enumerator"), "iterator", new DefaultValueExpression(new SimpleType("Enumerator"))));
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator")); factory.AddAnnotation(new ResolveResult(disposable));
            outer.Statements.Add(Set("iterator", factory));
            outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("ulong"), "found"));
            var body = new BlockStatement { new LabelStatement("again"),
                new VariableDeclarationStatement(new PrimitiveType("bool"), "advanced", Call("MoveNext")),
                Set("found", new ConditionalExpression(Id("advanced"), new PrimitiveExpression(1UL), new PrimitiveExpression(0UL))),
                new IfElseStatement(new UnaryOperatorExpression(UnaryOperatorType.Not, Id("advanced")), new BlockStatement { new BreakStatement() }),
                new VariableDeclarationStatement(new PrimitiveType("int"), "current", new MemberReferenceExpression(Id("iterator"), "Current")) };
            body.Statements.Add(new IfElseStatement(new InvocationExpression(Id("Skip"), Id("current")), new BlockStatement { new GotoStatement("again") }));
            body.Statements.Add(Set("matched", new InvocationExpression(Id("Match"), Id("current"))));
            if (mode == "result-read") body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"), Id("found"))));
            if (mode == "element-write") body.Statements.Add(Set("current", new PrimitiveExpression(0)));
            body.Statements.Add(new ContinueStatement());
            var loop = new DoWhileStatement { Condition = negate ? new UnaryOperatorExpression(UnaryOperatorType.Not, Id("matched")) : Id("matched"), EmbeddedStatement = body };
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement { new VariableDeclarationStatement(new PrimitiveType("bool"), "matched"), loop } };
            guarded.CatchClauses.Add(new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement { new ExpressionStatement(Call("Dispose")), new ThrowStatement(Id("error")) } });
            outer.Statements.Add(guarded); outer.Statements.Add(new ExpressionStatement(Call("Dispose")));
            if (mode == "enum-escape") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"), Id("iterator"))));
            if (mode == "extra-entry") outer.Statements.Add(new GotoStatement("again"));
            outer.Statements.Add(new ReturnStatement(Id("found")));
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).GetNestedType("RecoveredForeach", BindingFlags.NonPublic)!, nonPublic: true)!;
            transform.Run(tree, null!);
            a.Equal(mode == "valid" ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的查找和外泄边界");
            if (mode == "valid")
            {
                a.True(tree.Descendants.OfType<VariableInitializer>().Single(v => v.Name == "found").Initializer is PrimitiveExpression { Value: 0UL }, "耗尽返回零");
                a.True(tree.Descendants.OfType<AssignmentExpression>().Any(s => s.Left is IdentifierExpression { Identifier: "found" } && s.Right is PrimitiveExpression { Value: 1UL }), "提前退出置一");
                a.True(!tree.Descendants.OfType<GotoStatement>().Any() && tree.Descendants.OfType<ContinueStatement>().Count() == 2, "检查条件和跳过条件的路径均用结构化跳转");
                a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Current" or "Dispose"), "显式枚举收敛");
            }
        }
        return a.Finish("search-foreach");
    }
}
