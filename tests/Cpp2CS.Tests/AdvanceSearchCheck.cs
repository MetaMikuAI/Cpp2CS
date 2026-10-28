using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class AdvanceSearchCheck
{
    [Command("advance-search", "查找枚举的状态结果和首个读取边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var compilation = new CSharpDecompiler(typeof(AdvanceSearchCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        var a = new Assertions();
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Set(string name, Expression value) => new(new AssignmentExpression(Id(name), value));
        InvocationExpression Call(string name) => new(new MemberReferenceExpression(Id("iterator"), name));
        foreach (var mode in new[] { "valid", "different-state", "flag-escape", "enum-escape", "result-read", "preceding-call", "extra-catch", "wrong-one" })
        {
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "Subject" }; tree.Members.Add(type);
            var method = new MethodDeclaration { Name = "Contains", ReturnType = new PrimitiveType("bool"), Body = new BlockStatement() }; type.Members.Add(method);
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator"));
            factory.AddAnnotation(new ResolveResult(compilation.FindType(typeof(List<int>.Enumerator))));
            var outer = method.Body!;
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Enumerator"), "iterator", new DefaultValueExpression(new SimpleType("Enumerator"))));
            outer.Statements.Add(Set("iterator", factory));
            outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("ulong"), "carried"));
            outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("byte"), "state"));
            var found = mode == "different-state" ? 13 : 7;
            Expression predicate = new BinaryOperatorExpression(new MemberReferenceExpression(Id("iterator"), "Current"), BinaryOperatorType.Equality, Id(mode == "result-read" ? "state" : "requested"));
            if (mode == "preceding-call") predicate = new BinaryOperatorExpression(new InvocationExpression(Id("Observe")), BinaryOperatorType.ConditionalAnd, predicate);
            var positive = new BlockStatement { new IfElseStatement(new UnaryOperatorExpression(UnaryOperatorType.Not, predicate), new BlockStatement { new ContinueStatement() }), Set("state", new PrimitiveExpression(found)), new BreakStatement() };
            var body = new BlockStatement {
                new VariableDeclarationStatement(new PrimitiveType("bool"), "advanced", Call("MoveNext")),
                Set("carried", new ConditionalExpression(Id("advanced"), new PrimitiveExpression(mode == "wrong-one" ? 2UL : 1UL), new PrimitiveExpression(0UL))),
                new IfElseStatement(Id("advanced"), positive), Set("state", new PrimitiveExpression(found + 1)), new BreakStatement() };
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement { new ExpressionStatement(Call("Dispose")), new ThrowStatement(Id("error")) } };
            if (mode == "extra-catch") catcher.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Log"))));
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement { new WhileStatement(new PrimitiveExpression(true), body) } }; guarded.CatchClauses.Add(catcher);
            outer.Statements.Add(guarded); outer.Statements.Add(new ExpressionStatement(Call("Dispose")));
            if (mode is "flag-escape" or "enum-escape") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id(mode == "flag-escape" ? "advanced" : "iterator"))));
            outer.Statements.Add(new ReturnStatement(new BinaryOperatorExpression(new BinaryOperatorExpression(Id("carried"), BinaryOperatorType.BitwiseAnd,
                new ConditionalExpression(new BinaryOperatorExpression(Id("state"), BinaryOperatorType.Equality, new PrimitiveExpression(found)), new PrimitiveExpression(1UL), new PrimitiveExpression(0UL))), BinaryOperatorType.InEquality, new PrimitiveExpression(0UL))));
            var original = tree.ToString();
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).Assembly.GetType("Cpp2CS.Output.RecoveredForeach")!, nonPublic: true)!;
            transform.Run(tree, null!);
            var valid = mode is "valid" or "different-state";
            a.Equal(valid ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的查找边界");
            if (valid)
            {
                a.True(outer.Statements.Last() is ReturnStatement { Expression: PrimitiveExpression { Value: false } }, "耗尽返回 false");
                a.True(tree.Descendants.OfType<ForeachStatement>().Single().Descendants.OfType<ReturnStatement>().Single().Expression is PrimitiveExpression { Value: true }, "匹配返回 true");
                a.True(!tree.Descendants.OfType<LabelStatement>().Any() && !tree.Descendants.OfType<GotoStatement>().Any(), "无标签残留");
            }
            else a.Equal(original, tree.ToString(), "不匹配时保留原结构");
        }
        return a.Finish("advance-search");
    }
}
