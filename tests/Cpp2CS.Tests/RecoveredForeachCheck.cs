using System.Reflection;
using Cpp2CS.Output;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;

namespace Cpp2CS.Tests;

internal static class RecoveredForeachCheck
{
    [Command("recovered-foreach", "枚举器直接初始化与清理、逃逸边界", Gate = Gate.Unit)]
    public static int Run()
    {
        IdentifierExpression Id(string name) => new(name);
        MemberReferenceExpression Member(string name) => new(Id("iterator"), name);
        ExpressionStatement Dispose() => new(new InvocationExpression(Member("Dispose")));
        var a = new Assertions();
        foreach (var inline in new[] { false, true })
        foreach (var temporary in new[] { false, true })
        foreach (var escape in new[] { false, true })
        {
            var method = new MethodDeclaration { Name = "Visit", ReturnType = new PrimitiveType("void"), Body = new BlockStatement() };
            method.Parameters.Add(new ParameterDeclaration { Type = new SimpleType("object"), Name = "item" });
            var tree = new SyntaxTree();
            var type = new TypeDeclaration { Name = "Sample" };
            type.Members.Add(method);
            tree.Members.Add(type);
            method.Body.Statements.Add(new VariableDeclarationStatement(new SimpleType("Enumerator"), "iterator", new DefaultValueExpression(new SimpleType("Enumerator"))));
            var get = new InvocationExpression(new MemberReferenceExpression(Id("values"), "GetEnumerator"));
            if (temporary) method.Body.Statements.Add(new VariableDeclarationStatement(new SimpleType("var"), "saved", get));
            method.Body.Statements.Add(new ExpressionStatement(new AssignmentExpression(Id("iterator"), temporary ? Id("saved") : get)));
            var body = new BlockStatement();
            if (inline) body.Statements.Add(new ExpressionStatement(new InvocationExpression(new MemberReferenceExpression(Member("Current"), "Touch"))));
            else
            {
                body.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("int"), "current", Member("Current")));
                body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id("current"))));
            }
            body.Statements.Add(new ContinueStatement());
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement() };
            guarded.TryBlock.Statements.Add(new IfElseStatement(new InvocationExpression(Member("MoveNext")), body));
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement() };
            catcher.Body.Statements.Add(new ExpressionStatement(new AssignmentExpression(Id("pending"), Id("error"))));
            catcher.Body.Statements.Add(new GotoStatement("cleanup"));
            guarded.CatchClauses.Add(catcher);
            var loop = new BlockStatement();
            loop.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "pending"));
            loop.Statements.Add(guarded);
            loop.Statements.Add(new BreakStatement());
            loop.Statements.Add(new LabelStatement("cleanup"));
            loop.Statements.Add(Dispose());
            var returned = new BlockStatement();
            returned.Statements.Add(new ReturnStatement());
            loop.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(Id("pending"), BinaryOperatorType.Equality, new NullReferenceExpression()), returned));
            loop.Statements.Add(new ThrowStatement(Id("pending")));
            method.Body.Statements.Add(new WhileStatement(new PrimitiveExpression(true), loop));
            method.Body.Statements.Add(Dispose());
            if (escape) method.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Member("Current"))));
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).GetNestedType("RecoveredForeach", BindingFlags.NonPublic)!, nonPublic: true)!;
            transform.Run(tree, null!);
            a.Equal(escape ? 0 : 1, tree.Descendants.OfType<ForeachStatement>().Count(), "直接初始化和临时复制均折叠，枚举器逃逸时保留");
            if (!escape)
            {
                a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Dispose" or "Current"), "显式枚举与清理已全部收敛");
                if (inline) a.True(tree.ToString().Contains("item2"), "循环变量避开未使用的参数名");
            }
        }
        return a.Finish("recovered-foreach");
    }
}
