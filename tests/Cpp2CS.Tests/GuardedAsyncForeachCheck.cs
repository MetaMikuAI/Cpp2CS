using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class GuardedAsyncForeachCheck
{
    private sealed class Disposable : IDisposable { public void Dispose() { } }

    [Command("guarded-async-foreach", "异步枚举初始化标志、清理和局部逃逸", Gate = Gate.Unit)]
    public static int Run()
    {
        var typeSystem = new CSharpDecompiler(typeof(GuardedAsyncForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        var disposable = typeSystem.FindType(typeof(Disposable));
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Set(string name, Expression value) => new(new AssignmentExpression(Id(name), value));
        ExpressionStatement Flag(bool value) => Set("active", new PrimitiveExpression(value));
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "call-before", "enabled-before", "escape", "no-disposable", "current-write", "current-increment",
            "conditional", "conditional-call", "conditional-count", "conditional-extra" })
        {
            var method = new MethodDeclaration { Name = "Visit", Modifiers = Modifiers.Async, ReturnType = new SimpleType("Task"), Body = new BlockStatement() };
            method.Parameters.Add(new ParameterDeclaration { Type = new SimpleType("Collection"), Name = "values" });
            var tree = new SyntaxTree();
            var type = new TypeDeclaration { Name = "Subject" };
            type.Members.Add(method); tree.Members.Add(type);
            var outer = method.Body;
            outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("bool"), "active", new DefaultValueExpression(new PrimitiveType("bool"))));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Enumerator"), "iterator", new DefaultValueExpression(new SimpleType("Enumerator"))));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "pending"));
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement() };
            var contents = guarded.TryBlock.Statements;
            contents.Add(new VariableDeclarationStatement(new SimpleType("var"), "items", Id("values")));
            contents.Add(Flag(mode == "enabled-before"));
            if (mode == "call-before") contents.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"))));
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("items"), "GetEnumerator"));
            if (mode != "no-disposable") factory.AddAnnotation(new ResolveResult(mode.StartsWith("conditional", StringComparison.Ordinal)
                ? typeSystem.FindType(typeof(List<int>.Enumerator)) : disposable));
            contents.Add(new VariableDeclarationStatement(new SimpleType("var"), "created", factory));
            contents.Add(Flag(true));
            contents.Add(Set("iterator", Id("created")));
            var body = new BlockStatement();
            body.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("int"), "current", new MemberReferenceExpression(Id("iterator"), "Current")));
            body.Statements.Add(new ExpressionStatement(new UnaryOperatorExpression(UnaryOperatorType.Await, new InvocationExpression(Id("Suspend"), Id("current")))));
            if (mode == "current-write") body.Statements.Add(Set("current", new PrimitiveExpression(0)));
            if (mode == "current-increment") body.Statements.Add(new ExpressionStatement(new UnaryOperatorExpression(UnaryOperatorType.PostIncrement, Id("current"))));
            contents.Add(new WhileStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "MoveNext")), body));
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement() };
            catcher.Body.Statements.Add(new IfElseStatement(new UnaryOperatorExpression(UnaryOperatorType.Not, Id("active")), new BlockStatement { new ThrowStatement() }));
            catcher.Body.Statements.Add(Set("pending", Id("error")));
            catcher.Body.Statements.Add(new GotoStatement("cleanup"));
            guarded.CatchClauses.Add(catcher);
            outer.Statements.Add(guarded);
            outer.Statements.Add(Set("pending", new NullReferenceExpression()));
            outer.Statements.Add(new GotoStatement("cleanup"));
            outer.Statements.Add(new LabelStatement("cleanup"));
            outer.Statements.Add(new ExpressionStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "Dispose"))));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "exception", Id("pending")));
            var success = new BlockStatement { Set("iterator", new DefaultValueExpression(new SimpleType("Enumerator"))),
                new ExpressionStatement(new InvocationExpression(Id("Finish"))), new ReturnStatement() };
            if (mode == "escape") success.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"), Id("iterator"))));
            outer.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(Id("exception"), BinaryOperatorType.Equality, new NullReferenceExpression()), success));
            outer.Statements.Add(new ThrowStatement(Id("exception")));
            if (mode.StartsWith("conditional", StringComparison.Ordinal))
            {
                var source = (VariableDeclarationStatement)contents.First().Clone();
                if (mode == "conditional-call") source.Variables.Single().Initializer = new InvocationExpression(Id("Read"));
                var branch = new BlockStatement();
                foreach (var statement in contents.Skip(1)) branch.Statements.Add(statement.Clone());
                branch.Statements.Add(new GotoStatement("normal"));
                var count = new MemberReferenceExpression(Id("items"), "Count");
                var list = typeSystem.FindType(typeof(List<int>));
                if (mode != "conditional-count") count.AddAnnotation(new MemberResolveResult(new ResolveResult(list), list.GetProperties().Single(p => p.Name == "Count")));
                var condition = new BinaryOperatorExpression(new BinaryOperatorExpression(Id("items"), BinaryOperatorType.InEquality, new NullReferenceExpression()),
                    BinaryOperatorType.ConditionalAnd, new BinaryOperatorExpression(count, BinaryOperatorType.GreaterThanOrEqual, new PrimitiveExpression(1)));
                guarded.TryBlock = new BlockStatement { Flag(false), Flag(true), source, new IfElseStatement(condition, branch) };
                foreach (var statement in outer.Statements.SkipWhile(s => s != guarded).Skip(1).ToArray()) statement.Remove();
                outer.Statements.Add(new GotoStatement("end")); outer.Statements.Add(new LabelStatement("normal"));
                outer.Statements.Add(Set("pending", new NullReferenceExpression())); outer.Statements.Add(new GotoStatement("cleanup"));
                outer.Statements.Add(new LabelStatement("cleanup"));
                outer.Statements.Add(new ExpressionStatement(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "Dispose"))));
                outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "exception", Id("pending")));
                outer.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(Id("exception"), BinaryOperatorType.InEquality, new NullReferenceExpression()),
                    new BlockStatement { new ThrowStatement(Id("exception")) }));
                outer.Statements.Add(Set("iterator", new DefaultValueExpression(new SimpleType("Enumerator"))));
                if (mode == "conditional-extra") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Observe"))));
                outer.Statements.Add(new GotoStatement("end")); outer.Statements.Add(new LabelStatement("end")); outer.Statements.Add(new EmptyStatement());
            }
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).Assembly.GetType("Cpp2CS.Output.RecoveredForeach")!, nonPublic: true)!;
            transform.Run(tree, null!);
            a.Equal(mode is "valid" or "conditional" ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的清理与逃逸边界");
            a.Equal(1, tree.Descendants.OfType<UnaryOperatorExpression>().Count(e => e.Operator == UnaryOperatorType.Await), "await 保留一次且仍在循环内");
        }
        return a.Finish("guarded-async-foreach");
    }
}
