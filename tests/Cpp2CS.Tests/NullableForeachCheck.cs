using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class NullableForeachCheck
{
    [Command("nullable-foreach", "引用枚举器的条件清理和局部初始化边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var compilation = new CSharpDecompiler(typeof(NullableForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Set(string name, Expression value) => new(new AssignmentExpression(Id(name), value));
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "escape", "exception-escape", "external-jump", "outgoing-jump", "extra-catch", "throwing-prefix", "current-write", "return", "wrong-cleanup", "captured", "addressed", "direct" })
        {
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "Subject" }; tree.Members.Add(type);
            var method = new MethodDeclaration { Name = "Visit", ReturnType = new PrimitiveType("void"), Body = new BlockStatement() }; type.Members.Add(method);
            method.Parameters.Add(new ParameterDeclaration { Type = new PrimitiveType("int"), Name = "initial" });
            var outer = method.Body;
            if (mode == "captured") outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Func"), "read", new LambdaExpression { Body = Id("initial") }));
            if (mode == "addressed") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Mutate"), new DirectionExpression(FieldDirection.Ref, Id("initial")))));
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator"));
            factory.AddAnnotation(new ResolveResult(compilation.FindType(typeof(IEnumerator<int>))));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("var"), "iterator", factory));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "pending"));
            var content = new BlockStatement { new VariableDeclarationStatement(new PrimitiveType("int"), "current", new MemberReferenceExpression(Id("iterator"), "Current")),
                new ExpressionStatement(new InvocationExpression(Id("Use"), Id("current"), Id("total"))) };
            if (mode == "current-write") content.Statements.Add(Set("current", new PrimitiveExpression(0)));
            if (mode == "return") content.Statements.Add(new ReturnStatement());
            if (mode == "outgoing-jump") content.Statements.Add(new GotoStatement("cleanup"));
            var body = new BlockStatement {
                new IfElseStatement(new BinaryOperatorExpression(Id("iterator"), BinaryOperatorType.Equality, new NullReferenceExpression()),
                    new BlockStatement { new ThrowStatement(new ObjectCreateExpression(new SimpleType("NullReferenceException"))) }),
                new VariableDeclarationStatement(new PrimitiveType("int"), "total", mode == "throwing-prefix" ? new InvocationExpression(Id("Start")) : Id("initial")),
                new WhileStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "MoveNext")), content) };
            var guarded = new TryCatchStatement { TryBlock = body };
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement { Set("pending", Id("error")), new GotoStatement("cleanup") } };
            if (mode == "extra-catch") catcher.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Log"))));
            guarded.CatchClauses.Add(catcher); outer.Statements.Add(guarded);
            outer.Statements.Add(Set("pending", new NullReferenceExpression())); outer.Statements.Add(new GotoStatement("cleanup"));
            outer.Statements.Add(new LabelStatement("cleanup"));
            outer.Statements.Add(new ExpressionStatement(new UnaryOperatorExpression(UnaryOperatorType.NullConditionalRewrap,
                new InvocationExpression(new MemberReferenceExpression(new UnaryOperatorExpression(UnaryOperatorType.NullConditional, Id("iterator")), mode == "wrong-cleanup" ? "Close" : "Dispose")))));
            outer.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(Id("pending"), BinaryOperatorType.Equality, new NullReferenceExpression()), new BlockStatement { new ReturnStatement() }));
            outer.Statements.Add(new ThrowStatement(Id("pending")));
            if (mode is "escape" or "exception-escape") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"), Id(mode == "escape" ? "iterator" : "pending"))));
            if (mode == "external-jump") outer.Statements.Add(new GotoStatement("cleanup"));
            if (mode == "direct")
            {
                catcher.Body = new BlockStatement { new IfElseStatement(new BinaryOperatorExpression(Id("iterator"), BinaryOperatorType.Equality, new NullReferenceExpression()),
                    new BlockStatement { new ThrowStatement(Id("error")) }), new ExpressionStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "Dispose"))), new ThrowStatement(Id("error")) };
                foreach (var statement in outer.Statements.SkipWhile(s => s != guarded).Skip(1).ToArray()) statement.Remove();
                outer.Statements.Add(new ExpressionStatement(new UnaryOperatorExpression(UnaryOperatorType.NullConditionalRewrap,
                    new InvocationExpression(new MemberReferenceExpression(new UnaryOperatorExpression(UnaryOperatorType.NullConditional, Id("iterator")), "Dispose")))));
            }
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).GetNestedType("RecoveredForeach", BindingFlags.NonPublic)!, nonPublic: true)!;
            transform.Run(tree, null!);
            a.Equal(mode is "valid" or "direct" ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的清理边界");
            if (mode is "valid" or "direct")
            {
                a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Current" or "Dispose"), "显式枚举已消除");
                a.True(tree.Descendants.OfType<VariableInitializer>().Any(v => v.Name == "total" && v.Initializer is IdentifierExpression { Identifier: "initial" }), "保留局部初始化");
                a.True(!tree.Descendants.OfType<TryCatchStatement>().Any() && !tree.Descendants.OfType<GotoStatement>().Any(), "共享异常清理已折叠");
            }
        }
        return a.Finish("nullable-foreach");
    }
}
