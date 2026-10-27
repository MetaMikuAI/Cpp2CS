using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class AdvanceResultForeachCheck
{
    [Command("advance-result-foreach", "枚举耗尽、提前退出与清理后状态传递", Gate = Gate.Unit)]
    public static int Run()
    {
        var compilation = new CSharpDecompiler(typeof(AdvanceResultForeachCheck).Assembly.Location, new DecompilerSettings()).TypeSystem;
        IdentifierExpression Id(string name) => new(name);
        ExpressionStatement Set(string name, Expression value) => new(new AssignmentExpression(Id(name), value));
        ExpressionStatement Call(string name) => new(new InvocationExpression(new MemberReferenceExpression(Id("iterator"), name)));
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "escape", "read-result", "write-current", "captured", "extra-catch", "wrong-zero", "throwing-prefix", "outer-observer" })
        {
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "Subject" }; tree.Members.Add(type);
            var method = new MethodDeclaration { Name = "Visit", ReturnType = new PrimitiveType("void"), Body = new BlockStatement() }; type.Members.Add(method);
            var outer = method.Body; outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("int"), "initial", new PrimitiveExpression(0)));
            if (mode == "captured") outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("Func"), "read", new LambdaExpression { Body = Id("initial") }));
            var factory = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator"));
            factory.AddAnnotation(new ResolveResult(compilation.FindType(typeof(IEnumerator<int>))));
            outer.Statements.Add(new VariableDeclarationStatement(new SimpleType("var"), "iterator", factory));
            outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("int"), "next", mode == "throwing-prefix" ? new InvocationExpression(Id("Start"))
                : new BinaryOperatorExpression(Id("initial"), BinaryOperatorType.Add, new PrimitiveExpression(1))));
            outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("int"), "sum"));
            outer.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("ulong"), "result"));
            var positive = new BlockStatement { new VariableDeclarationStatement(new PrimitiveType("int"), "current", new MemberReferenceExpression(Id("iterator"), "Current")),
                new IfElseStatement(new InvocationExpression(Id("Keep"), Id("current")), new BlockStatement { new ContinueStatement() }) };
            if (mode == "read-result") positive.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id("result"))));
            if (mode == "write-current") positive.Statements.Add(Set("current", new PrimitiveExpression(0)));
            positive.Statements.Add(Set("state", Id("value"))); positive.Statements.Add(new BreakStatement());
            var loop = new WhileStatement(new PrimitiveExpression(true), new BlockStatement {
                new VariableDeclarationStatement(new PrimitiveType("bool"), "flag", new InvocationExpression(new MemberReferenceExpression(Id("iterator"), "MoveNext"))),
                new VariableDeclarationStatement(new PrimitiveType("ulong"), "value", new ConditionalExpression(Id("flag"), new PrimitiveExpression(1UL), new PrimitiveExpression(0UL))),
                new IfElseStatement(Id("flag"), positive), Set("state", new PrimitiveExpression(mode == "wrong-zero" ? 1UL : 0UL)), new BreakStatement() });
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement {
                new IfElseStatement(new BinaryOperatorExpression(Id("iterator"), BinaryOperatorType.Equality, new NullReferenceExpression()), new BlockStatement { new ThrowStatement(new ObjectCreateExpression(new SimpleType("NullReferenceException"))) }),
                Set("sum", Id("next")), new VariableDeclarationStatement(new PrimitiveType("ulong"), "state"), loop, Set("result", Id("state")) } };
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement {
                new IfElseStatement(new BinaryOperatorExpression(Id("iterator"), BinaryOperatorType.InEquality, new NullReferenceExpression()), new BlockStatement { Call("Dispose"), new ThrowStatement(Id("error")) }), new ThrowStatement(Id("error")) } };
            if (mode == "extra-catch") catcher.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Log"))));
            guarded.CatchClauses.Add(catcher); outer.Statements.Add(guarded); outer.Statements.Add(Call("Dispose"));
            outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id("result"), Id("sum"))));
            if (mode == "escape") outer.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id("iterator"))));
            if (mode == "outer-observer")
            {
                outer.Remove();
                var wrapper = new TryCatchStatement { TryBlock = outer }; method.Body = new BlockStatement { wrapper };
                wrapper.CatchClauses.Add(new CatchClause { Type = new SimpleType("Exception"), VariableName = "observed", Body = new BlockStatement { new ExpressionStatement(new InvocationExpression(Id("Use"), Id("sum"))) } });
            }
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).GetNestedType("RecoveredForeach", BindingFlags.NonPublic)!, nonPublic: true)!;
            transform.Run(tree, null!);
            a.Equal(mode == "valid" ? 1 : 0, tree.Descendants.OfType<ForeachStatement>().Count(), $"{mode} 的结果和副作用边界");
            if (mode != "valid") continue;
            a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Dispose" or "Current"), "显式枚举已折叠");
            a.True(tree.Descendants.OfType<VariableInitializer>().Single(v => v.Name == "result").Initializer is PrimitiveExpression { Value: 0UL }, "耗尽保持零");
            a.True(tree.Descendants.OfType<ForeachStatement>().Single().Descendants.OfType<AssignmentExpression>().Any(x => x.Left.ToString() == "result" && x.Right is PrimitiveExpression { Value: 1UL }), "提前退出保持一");
        }
        return a.Finish("advance-result-foreach");
    }
}
