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
        foreach (var mode in new[] { "local", "receiver", "projection", "conditional", "conditional-rewrap", "increment", "unresolved-argument" })
        foreach (var cleanupMode in new[] { "external", "internal", "continuation", "direct", "catch", "internal-catch", "catch-continuation" })
        foreach (var temporary in new[] { false, true })
        foreach (var escape in new[] { false, true })
        foreach (var earlyExit in cleanupMode is "external" or "direct" && mode == "local" && !temporary ? new[] { false, true } : new[] { false })
        {
            var internalCleanup = cleanupMode is "internal" or "internal-catch";
            var directCatch = cleanupMode is "catch" or "internal-catch";
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
            if (mode == "unresolved-argument") body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Member("Current"))));
            else if (mode is "conditional" or "conditional-rewrap" or "increment")
            {
                var operand = new UnaryOperatorExpression(mode == "increment" ? UnaryOperatorType.PostIncrement : UnaryOperatorType.NullConditional, Member("Current"));
                Expression call = new InvocationExpression(new MemberReferenceExpression(operand, "Touch"));
                if (mode == "conditional-rewrap") call = new UnaryOperatorExpression(UnaryOperatorType.NullConditionalRewrap, call);
                body.Statements.Add(new ExpressionStatement(call));
            }
            else if (mode == "receiver") body.Statements.Add(new ExpressionStatement(new InvocationExpression(new MemberReferenceExpression(Member("Current"), "Touch"))));
            else if (mode == "projection") body.Statements.Add(new VariableDeclarationStatement(new SimpleType("var"), "key", new MemberReferenceExpression(Member("Current"), "Key")));
            else
            {
                body.Statements.Add(new VariableDeclarationStatement(new PrimitiveType("int"), "current", Member("Current")));
                body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Id("current"))));
            }
            body.Statements.Add(new ContinueStatement());
            var guarded = new TryCatchStatement { TryBlock = new BlockStatement() };
            if (earlyExit)
            {
                var exhausted = new BlockStatement();
                exhausted.Statements.Add(new BreakStatement());
                guarded.TryBlock.Statements.Add(new IfElseStatement(new UnaryOperatorExpression(UnaryOperatorType.Not, new InvocationExpression(Member("MoveNext"))), exhausted));
                foreach (var statement in body.Statements) guarded.TryBlock.Statements.Add(statement.Clone());
            }
            else guarded.TryBlock.Statements.Add(new IfElseStatement(new InvocationExpression(Member("MoveNext")), body));
            var catcher = new CatchClause { Type = new SimpleType("Exception"), VariableName = "error", Body = new BlockStatement() };
            if (directCatch)
            {
                catcher.Body.Statements.Add(Dispose());
                catcher.Body.Statements.Add(new ThrowStatement(Id("error")));
            }
            else
            {
                catcher.Body.Statements.Add(new ExpressionStatement(new AssignmentExpression(Id(cleanupMode == "catch-continuation" ? "merged" : "pending"), Id("error"))));
                catcher.Body.Statements.Add(cleanupMode == "catch-continuation" ? new BreakStatement() : new GotoStatement("cleanup"));
            }
            guarded.CatchClauses.Add(catcher);
            var loop = new BlockStatement();
            loop.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "pending"));
            loop.Statements.Add(guarded);
            if (cleanupMode is "continuation" or "catch-continuation")
            {
                method.Body.Statements.Add(new VariableDeclarationStatement(new SimpleType("Exception"), "merged"));
                loop.Statements.Add(new ExpressionStatement(new AssignmentExpression(Id("merged"), new NullReferenceExpression())));
                loop.Statements.Add(new BreakStatement());
                if (cleanupMode == "continuation")
                {
                    loop.Statements.Add(new LabelStatement("cleanup"));
                    loop.Statements.Add(new ExpressionStatement(new AssignmentExpression(Id("merged"), Id("pending"))));
                    loop.Statements.Add(new BreakStatement());
                }
            }
            else if (directCatch)
            {
                if (internalCleanup) loop.Statements.Add(Dispose());
                loop.Statements.Add(new BreakStatement());
            }
            else
            {
                if (internalCleanup) loop.Statements.Add(Dispose());
                if (!earlyExit) loop.Statements.Add(new BreakStatement());
                loop.Statements.Add(new LabelStatement("cleanup"));
                loop.Statements.Add(Dispose());
                var returned = new BlockStatement();
                returned.Statements.Add(internalCleanup ? new BreakStatement() : new ReturnStatement());
                if (cleanupMode != "direct") loop.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(Id("pending"), BinaryOperatorType.Equality, new NullReferenceExpression()), returned));
                loop.Statements.Add(new ThrowStatement(Id("pending")));
            }
            method.Body.Statements.Add(new WhileStatement(new PrimitiveExpression(true), loop));
            if (!internalCleanup) method.Body.Statements.Add(Dispose());
            if (cleanupMode is "continuation" or "catch-continuation")
            {
                var success = new BlockStatement();
                success.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Finish"))));
                method.Body.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(Id("merged"), BinaryOperatorType.Equality, new NullReferenceExpression()), success));
                method.Body.Statements.Add(new ThrowStatement(Id("merged")));
            }
            if (escape) method.Body.Statements.Add(new ExpressionStatement(new InvocationExpression(Id("Use"), Member("Current"))));
            var transform = (IAstTransform)Activator.CreateInstance(typeof(Decompilation).Assembly.GetType("Cpp2CS.Output.RecoveredForeach")!, nonPublic: true)!;
            if (cleanupMode == "catch" && !temporary && !escape)
            {
                foreach (var returns in new[] { false, true })
                {
                    var direct = (SyntaxTree)tree.Clone();
                    var directLoop = direct.Descendants.OfType<WhileStatement>().Single();
                    var directGuard = directLoop.Descendants.OfType<TryCatchStatement>().Single();
                    var selection = directGuard.TryBlock!.Statements.OfType<IfElseStatement>().Single();
                    var directBody = (BlockStatement)selection.TrueStatement.Clone();
                    directBody.Statements.Last().Remove();
                    if (returns) directBody.Statements.Add(new ReturnStatement());
                    var copiedGuard = (TryCatchStatement)directGuard.Clone();
                    copiedGuard.TryBlock = new BlockStatement { new WhileStatement(selection.Condition!.Clone(), directBody) };
                    var directParent = (BlockStatement)directLoop.Parent!;
                    directParent.Statements.InsertBefore(directLoop, new VariableDeclarationStatement(new PrimitiveType("int"), "total", new PrimitiveExpression(0)));
                    directLoop.ReplaceWith(copiedGuard);
                    transform.Run(direct, null!);
                    a.Equal(returns || mode is "increment" or "unresolved-argument" ? 0 : 1, direct.Descendants.OfType<ForeachStatement>().Count(), "完整保护循环可折叠，越过清理的 return 保留");
                    if (returns) a.True(direct.Descendants.OfType<WhileStatement>().Single().Condition is InvocationExpression, "未折叠时保留原循环形态");
                }
            }
            if (escape && mode == "local" && cleanupMode == "external" && !temporary)
            {
                foreach (var placement in new[] { "after", "before", "label" })
                {
                    var reused = (SyntaxTree)tree.Clone();
                    var statements = reused.Descendants.OfType<MethodDeclaration>().Single().Body!.Statements;
                    var reset = new ExpressionStatement(new AssignmentExpression(Id("iterator"), new InvocationExpression(new MemberReferenceExpression(Id("other"), "GetEnumerator"))));
                    statements.InsertBefore(placement == "before" ? statements.ElementAt(1) : statements.Last(), reset);
                    if (placement == "label") statements.InsertBefore(statements.Last(), new LabelStatement("skipReset"));
                    transform.Run(reused, null!);
                    a.Equal(placement == "after" ? 1 : 0, reused.Descendants.OfType<ForeachStatement>().Count(), "后续读取须由新的无跳转初始化支配");
                }
            }
            transform.Run(tree, null!);
            a.Equal(escape || mode is "increment" or "unresolved-argument" ? 0 : 1, tree.Descendants.OfType<ForeachStatement>().Count(), "直接初始化和临时复制均折叠，逃逸、读取被修改或调用目标不明时保留");
            if (!escape && mode is not ("increment" or "unresolved-argument"))
            {
                a.True(!tree.Descendants.OfType<MemberReferenceExpression>().Any(m => m.MemberName is "MoveNext" or "Dispose" or "Current"), "显式枚举与清理已全部收敛");
                if (mode != "local") a.True(tree.ToString().Contains("item2"), "循环变量避开未使用的参数名");
            }
        }
        return a.Finish("recovered-foreach");
    }
}
