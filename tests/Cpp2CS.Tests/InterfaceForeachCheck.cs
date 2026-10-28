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
    public static void Use(string? value) { }

    [Command("interface-foreach", "非泛型枚举器的接口清理及逃逸边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var compilation = new CSharpDecompiler(typeof(InterfaceForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        var a = new Assertions();
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Dispose(string name) => new(new InvocationExpression(new MemberReferenceExpression(Id(name), "Dispose")));
        foreach (var mode in new[] { "valid", "typed", "inline-typed", "late-typed", "typed-escape", "escape", "cleanup-escape", "extra-cleanup", "wrong-interface", "wrong-receiver", "wrong-return-type", "wrong-dispose", "extra-catch" })
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
            if (mode.Contains("typed"))
            {
                var content = (BlockStatement)((WhileStatement)guarded.TryBlock.Statements.Single()).EmbeddedStatement;
                var declaration = (VariableDeclarationStatement)content.Statements.First();
                var read = (MemberReferenceExpression)declaration.Variables.Single().Initializer!;
                var iteratorType = compilation.FindType(typeof(System.Collections.IEnumerator));
                read.AddAnnotation(new MemberResolveResult(new ResolveResult(iteratorType), iteratorType.GetProperties().Single(p => p.Name == "Current")));
                read.Remove();
                var cast = new CastExpression(new PrimitiveType("string"), read);
                cast.AddAnnotation(new ResolveResult(compilation.FindType(typeof(string))));
                declaration.Type = new PrimitiveType("string");
                declaration.Variables.Single().Initializer = cast;
                if (mode != "typed")
                {
                    declaration.Remove(); cast.Remove();
                    var use = Id("Use");
                    use.AddAnnotation(new MemberResolveResult(null, compilation.FindType(typeof(InterfaceForeachCheck)).GetMethods().Single(m => m.Name == "Use")));
                    var call = new InvocationExpression(use, cast);
                    call.AddAnnotation(new MemberResolveResult(null, compilation.FindType(typeof(InterfaceForeachCheck)).GetMethods().Single(m => m.Name == "Use")));
                    if (mode == "late-typed") call.Arguments.InsertBefore(cast, new InvocationExpression(Id("Effect")));
                    content.Statements.Single().ReplaceWith(new ExpressionStatement(call));
                }
            }
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement {
                new IfElseStatement(new UnaryOperatorExpression(UnaryOperatorType.Not, new ParenthesizedExpression(Pattern("failure"))),
                    new BlockStatement { new ThrowStatement(Id("error")) }), Dispose("failure"), new ThrowStatement(Id("error")) } };
            if (mode == "extra-catch") catcher.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Log"))));
            guarded.CatchClauses.Add(catcher); method.Body.Statements.Add(guarded);
            var cleanup = new BlockStatement { Dispose(mode == "wrong-dispose" ? "other" : "success") };
            if (mode == "extra-cleanup") cleanup.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Log"))));
            method.Body.Statements.Add(new IfElseStatement(Pattern("success"), cleanup));
            if (mode is "escape" or "cleanup-escape" or "typed-escape") method.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"), Id(mode == "cleanup-escape" ? "success" : "iterator"))));
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).Assembly.GetType("Cpp2CS.Output.RecoveredForeach")!, nonPublic: true)!;
            transform.Run(tree, null!);
            var folded = mode is "valid" or "typed" or "inline-typed";
            a.Equal(folded ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的条件释放边界");
            if (folded) a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Current" or "Dispose"), "枚举及释放已折叠");
            if (mode is "typed" or "inline-typed") a.Equal("string", tree.Descendants.OfType<ForeachStatement>().SingleOrDefault()?.VariableType.ToString(), "foreach 保留显式转换的类型");
            if (mode == "typed-escape") a.True(!tree.Descendants.OfType<VariableInitializer>().Any(v => v.Name == "item"), "未折叠时还原内联表达式");
        }
        return a.Finish("interface-foreach");
    }
}
