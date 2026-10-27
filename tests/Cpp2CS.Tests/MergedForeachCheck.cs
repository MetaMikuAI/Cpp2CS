using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class MergedForeachCheck
{
    private sealed class Disposable : IDisposable { public void Dispose() { } }

    [Command("merged-foreach", "共享枚举清理、元素写入和跳转边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var typeSystem = new CSharpDecompiler(typeof(MergedForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        var disposable = typeSystem.FindType(typeof(Disposable));
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Set(string name, Expression value) => new(new AssignmentExpression(Id(name), value));
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "write", "ref", "increment", "escape", "exception-escape", "external-jump", "outgoing-jump", "extra-catch", "no-disposable" })
        {
            var method = new MethodDeclaration { Name = "Visit", ReturnType = new PrimitiveType("void"), Body = new BlockStatement() };
            method.Parameters.Add(new ParameterDeclaration { Type = new SimpleType("object"), Name = "item" });
            var tree = new SyntaxTree();
            var type = new TypeDeclaration { Name = "Subject" };
            type.Members.Add(method); tree.Members.Add(type);
            var outer = method.Body;
            if (mode == "external-jump") outer.Statements.Add(new GotoStatement("cleanup"));
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator"));
            if (mode != "no-disposable") factory.AddAnnotation(new ResolveResult(disposable));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("var"), "iterator", factory));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "pending"));
            var body = new BlockStatement { new VariableDeclarationStatement(new PrimitiveType("int"), "current", new MemberReferenceExpression(Id("iterator"), "Current")),
                new ExpressionStatement(new InvocationExpression(Id("Use"), Id("current"))) };
            if (mode == "write") body.Statements.Add(Set("current", new PrimitiveExpression(0)));
            if (mode == "ref") body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Mutate"), new DirectionExpression(FieldDirection.Ref, Id("current")))));
            if (mode == "increment") body.Statements.Add(new ExpressionStatement(new UnaryOperatorExpression(UnaryOperatorType.PostIncrement, Id("current"))));
            if (mode == "outgoing-jump") body.Statements.Add(new GotoStatement("cleanup"));
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement { new WhileStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "MoveNext")), body) } };
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement { Set("pending", Id("error")), new GotoStatement("cleanup") } };
            if (mode == "extra-catch") catcher.Body.Statements.InsertBefore(catcher.Body.Statements.First(), new ExpressionStatement(new InvocationExpression(Id("Log"))));
            guarded.CatchClauses.Add(catcher); outer.Statements.Add(guarded);
            outer.Statements.Add(Set("pending", new NullReferenceExpression()));
            outer.Statements.Add(new GotoStatement("cleanup"));
            outer.Statements.Add(new LabelStatement("cleanup"));
            outer.Statements.Add(new ExpressionStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "Dispose"))));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "exception", Id("pending")));
            outer.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(Id("exception"), BinaryOperatorType.InEquality, new NullReferenceExpression()), new BlockStatement { new ThrowStatement(Id("exception")) }));
            outer.Statements.Add(Set("iterator", new DefaultValueExpression(new SimpleType("Enumerator"))));
            outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Finish"))));
            if (mode is "escape" or "exception-escape") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"), Id(mode == "escape" ? "iterator" : "exception"))));
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).GetNestedType("RecoveredForeach", BindingFlags.NonPublic)!, nonPublic: true)!;
            transform.Run(tree, null!);
            var expected = mode is "valid" or "write" or "ref" or "increment";
            a.Equal(expected ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的清理与逃逸边界");
            if (expected)
            {
                a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Dispose" or "Current"), "显式枚举已折叠");
                a.True(method.Body.Statements.Last().ToString().Contains("Finish"), "正常后续工作保留");
                if (mode != "valid") a.True(tree.ToString().Contains("current = item2"), "写入使用独立局部并避开参数名");
            }
        }
        return a.Finish("merged-foreach");
    }
}
