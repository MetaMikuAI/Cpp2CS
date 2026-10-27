using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class ResultForeachCheck
{
    private sealed class Disposable : IDisposable { public void Dispose() { } }
    [Command("result-foreach", "枚举耗尽结果、正常退出标签与局部使用边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var compilation = new CSharpDecompiler(typeof(ResultForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Set(string name, Expression value) => new(new AssignmentExpression(Id(name), value));
        InvocationExpression Call(string member) => new(new MemberReferenceExpression(Id("iterator"), member));
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "valid-mask", "result-read", "escape", "extra-entry", "current-write", "wrong-cleanup" })
        {
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "Subject" }; tree.Members.Add(type);
            var method = new MethodDeclaration { Name = "Find", ReturnType = new PrimitiveType("bool"), Body = new BlockStatement() }; type.Members.Add(method);
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator"));
            factory.AddAnnotation(new ResolveResult(compilation.FindType(typeof(Disposable))));
            var outer = method.Body;
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Enumerator"), "iterator", new DefaultValueExpression(new SimpleType("Enumerator"))));
            outer.Statements.Add(Set("iterator", factory)); outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("bool"), "found"));
            if (mode == "valid-mask") outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("byte"), "status"));
            var positive = new BlockStatement { new VariableDeclarationStatement(new PrimitiveType("int"), "current", new MemberReferenceExpression(Id("iterator"), "Current")) };
            if (mode == "result-read") positive.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id("found"))));
            if (mode == "current-write") positive.Statements.Add(Set("current", new PrimitiveExpression(0)));
            var matched = new BlockStatement { Set("found", new PrimitiveExpression(true)) };
            if (mode == "valid-mask") matched.Statements.Add(Set("status", new PrimitiveExpression(5)));
            matched.Statements.Add(new GotoStatement("finished"));
            if (mode == "valid-mask")
            {
                var selection = new SwitchStatement { Expression = Id("current") };
                var section = new SwitchSection(); section.CaseLabels.Add(new CaseLabel(new PrimitiveExpression(1)));
                foreach (var statement in matched.Statements.ToArray()) { statement.Remove(); section.Statements.Add(statement); }
                selection.SwitchSections.Add(section); positive.Statements.Add(selection);
            }
            else positive.Statements.Add(new IfElseStatement(new InvocationExpression(Id("Match"), Id("current")), matched));
            positive.Statements.Add(new ContinueStatement());
            var body = new BlockStatement { new IfElseStatement(Call("MoveNext"), positive), Set("found", new PrimitiveExpression(false)), new BreakStatement(), new ContinueStatement(), new LabelStatement("finished"), new BreakStatement() };
            if (mode == "valid-mask") body.Statements.InsertBefore(body.Statements.OfType<BreakStatement>().First(), Set("status", new PrimitiveExpression(6)));
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement { new WhileStatement(new PrimitiveExpression(true), body) } };
            guarded.CatchClauses.Add(new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement { new ExpressionStatement(Call(mode == "wrong-cleanup" ? "Close" : "Dispose")), new ThrowStatement(Id("error")) } });
            outer.Statements.Add(guarded); outer.Statements.Add(new ExpressionStatement(Call("Dispose")));
            if (mode == "escape") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id("iterator"))));
            if (mode == "extra-entry") outer.Statements.Add(new GotoStatement("finished"));
            Expression result = Id("found");
            if (mode == "valid-mask") result = new BinaryOperatorExpression(new CastExpression(new PrimitiveType("byte"), new BinaryOperatorExpression(
                new ConditionalExpression(Id("found"), new PrimitiveExpression(1U), new PrimitiveExpression(0U)), BinaryOperatorType.BitwiseAnd,
                new ConditionalExpression(new BinaryOperatorExpression(Id("status"), BinaryOperatorType.Equality, new PrimitiveExpression(5)), new PrimitiveExpression(1U), new PrimitiveExpression(0U)))), BinaryOperatorType.InEquality, new PrimitiveExpression(0));
            outer.Statements.Add(new ReturnStatement(result));
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).GetNestedType("RecoveredForeach", BindingFlags.NonPublic)!, nonPublic: true)!;
            transform.Run(tree, null!);
            a.Equal(mode is "valid" or "valid-mask" ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的退出与使用边界");
            if (mode is "valid" or "valid-mask")
            {
                a.True(outer.Statements.Last() is ReturnStatement { Expression: PrimitiveExpression { Value: false } }, "耗尽返回 false");
                a.True(tree.Descendants.OfType<ForeachStatement>().Single().Descendants.OfType<ReturnStatement>().Single().Expression is PrimitiveExpression { Value: true }, "匹配后经过隐式清理返回 true");
                a.True(!tree.Descendants.OfType<LabelStatement>().Any() && !tree.Descendants.OfType<GotoStatement>().Any(), "结果状态和退出标签消除");
                a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Dispose" or "Current"), "显式枚举收敛");
            }
        }
        return a.Finish("result-foreach");
    }
}
