using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class InterfaceForeachCheck
{
    [Command("interface-foreach", "非泛型枚举器的接口清理及逃逸边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var compilation = new CSharpDecompiler(typeof(InterfaceForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        var a = new Assertions();
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Dispose(string name) => new(new InvocationExpression(new MemberReferenceExpression(Id(name), "Dispose")));
        foreach (var mode in new[] { "valid", "escape", "cleanup-escape", "extra-cleanup", "wrong-interface", "wrong-receiver", "wrong-return-type", "wrong-dispose", "extra-catch" })
        {
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "Subject" }; tree.Members.Add(type);
            var method = new MethodDeclaration { Name = "Visit", ReturnType = new PrimitiveType("void"), Body = new BlockStatement() }; type.Members.Add(method);
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator"));
            factory.AddAnnotation(new ResolveResult(compilation.FindType(mode == "wrong-return-type" ? typeof(object) : typeof(System.Collections.IEnumerator))));
            method.Body.Statements.Add(new VariableDeclarationStatement(new SimpleType("IEnumerator"), "iterator", factory));
            Expression Pattern(string name)
            {
                var patternType = new SimpleType("IDisposable");
                patternType.AddAnnotation(new ResolveResult(compilation.FindType(mode == "wrong-interface" ? typeof(ICloneable) : typeof(IDisposable))));
                return new BinaryOperatorExpression(Id(mode == "wrong-receiver" ? "other" : "iterator"), BinaryOperatorType.IsPattern,
                    new DeclarationExpression { Type = patternType, Designation = new SingleVariableDesignation(name) });
            }
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement {
                new WhileStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "MoveNext")), new BlockStatement {
                    new VariableDeclarationStatement(new PrimitiveType("object"), "current", new MemberReferenceExpression(Id("iterator"), "Current")),
                    new ExpressionStatement(new InvocationExpression(Id("Use"), Id("current"))) }) } };
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement {
                new IfElseStatement(new UnaryOperatorExpression(UnaryOperatorType.Not, new ParenthesizedExpression(Pattern("failure"))),
                    new BlockStatement { new ThrowStatement(Id("error")) }), Dispose("failure"), new ThrowStatement(Id("error")) } };
            if (mode == "extra-catch") catcher.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Log"))));
            guarded.CatchClauses.Add(catcher); method.Body.Statements.Add(guarded);
            var cleanup = new BlockStatement { Dispose(mode == "wrong-dispose" ? "other" : "success") };
            if (mode == "extra-cleanup") cleanup.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Log"))));
            method.Body.Statements.Add(new IfElseStatement(Pattern("success"), cleanup));
            if (mode is "escape" or "cleanup-escape") method.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"), Id(mode == "escape" ? "iterator" : "success"))));
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).GetNestedType("RecoveredForeach", BindingFlags.NonPublic)!, nonPublic: true)!;
            transform.Run(tree, null!);
            a.Equal(mode == "valid" ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的条件释放边界");
            if (mode == "valid") a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Current" or "Dispose"), "枚举及释放已折叠");
        }
        return a.Finish("interface-foreach");
    }
}
