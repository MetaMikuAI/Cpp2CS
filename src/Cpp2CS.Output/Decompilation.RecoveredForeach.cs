using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>把枚举器的正常清理与捕获后清理配对，恢复 foreach 的隐式 finally。</summary>
    private sealed partial class RecoveredForeach : IAstTransform
    {
        private static bool Name(Expression? expression, string? name) => expression is IdentifierExpression id && id.Identifier == name;
        private static bool Dispose(Statement statement, string name) => statement is ExpressionStatement
            { Expression: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "Dispose", Target: var receiver } } }
            && Name(receiver, name);
        private static bool Set(Statement statement, string target, string? source) => statement is ExpressionStatement
            { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var left, Right: var right } }
            && Name(left, target) && (source is null ? right is NullReferenceExpression : Name(right, source));
        private static bool NullTest(Expression? expression, string name, BinaryOperatorType op) => expression is BinaryOperatorExpression b
            && b.Operator == op && Name(b.Left, name) && b.Right is NullReferenceExpression;

        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var loop in rootNode.Descendants.OfType<WhileStatement>().ToArray())
            {
                if (loop.Parent is not BlockStatement parent || loop.Condition is not PrimitiveExpression { Value: true }
                    || loop.EmbeddedStatement is not BlockStatement content) continue;
                var parts = content.Statements.ToArray();
                if (parts.OfType<TryCatchStatement>().ToArray() is not [var guarded]
                    || guarded.FinallyBlock is not null || guarded.CatchClauses.Count != 1
                    || guarded.TryBlock is not { } tryBlock || tryBlock.Statements.ToArray() is not [IfElseStatement test] || test.FalseStatement is not null
                    || test.Condition is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression
                        { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }
                    || test.TrueStatement is not BlockStatement body || body.Statements.LastOrDefault() is not ContinueStatement
                    || body.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.Count != 1
                    || current.Variables.Single().Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var read }
                    || !Name(read, enumerator.Identifier)) continue;
                var name = enumerator.Identifier;
                var catcher = guarded.CatchClauses.Single();
                if (catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                    || catcher.Body is not { } catchBody || catchBody.Statements.ToArray() is not [ExpressionStatement { Expression: AssignmentExpression
                        { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression saved, Right: var caught } }, GotoStatement jump]
                    || !Name(caught, catcher.VariableName)) continue;
                var before = parts.TakeWhile(s => s != guarded).ToArray();
                if (before.Any(s => s is not VariableDeclarationStatement d || d.Variables.Any(v => v.Initializer is not null))) continue;
                var tail = parts.SkipWhile(s => s != guarded).Skip(1).ToArray();
                var siblings = parent.Statements.ToArray();
                var index = Array.IndexOf(siblings, loop);
                if (index + 1 >= siblings.Length || !Dispose(siblings[index + 1], name)) continue;
                var removed = new List<Statement> { siblings[index + 1] };
                if (tail is [BreakStatement, LabelStatement label, var cleanup, IfElseStatement empty, ThrowStatement thrown]
                    && label.Label == jump.Label && Dispose(cleanup, name) && NullTest(empty.Condition, saved.Identifier, BinaryOperatorType.Equality)
                    && empty.FalseStatement is null && empty.TrueStatement is BlockStatement { Statements.Count: 1 } emptyBody
                    && emptyBody.Statements.Single() is ReturnStatement { Expression: null } && Name(thrown.Expression, saved.Identifier)) { }
                else if (tail is [ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression merged } }, BreakStatement,
                    LabelStatement mergeLabel, var copy, BreakStatement] && mergeLabel.Label == jump.Label
                    && Set(tail[0], merged.Identifier, null) && Set(copy, merged.Identifier, saved.Identifier)
                    && index + 2 < siblings.Length && siblings[index + 2] is IfElseStatement rethrow
                    && rethrow.FalseStatement is null && NullTest(rethrow.Condition, merged.Identifier, BinaryOperatorType.InEquality)
                    && rethrow.TrueStatement is BlockStatement { Statements.Count: 1 } throwBody
                    && throwBody.Statements.Single() is ThrowStatement finalThrow && Name(finalThrow.Expression, merged.Identifier))
                    removed.Add(rethrow);
                else continue;
                // 只接收元素读取以外不使用枚举器的循环体。
                if (body.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == name) != 1) continue;
                var prefix = siblings.Take(index).Reverse().SkipWhile(s => s is VariableDeclarationStatement d && d.Variables.All(v => v.Initializer is null)).ToArray();
                if (prefix.FirstOrDefault() is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                    Left: var destination, Right: var initialized } } assignment || !Name(destination, name)) continue;
                VariableDeclarationStatement? factory = null;
                IdentifierExpression? temporary = null;
                if (initialized is IdentifierExpression copied && prefix.ElementAtOrDefault(1) is VariableDeclarationStatement declarationFactory
                    && declarationFactory.Variables.Count == 1 && declarationFactory.Variables.Single().Name == copied.Identifier)
                {
                    temporary = copied;
                    factory = declarationFactory;
                    initialized = factory.Variables.Single().Initializer;
                }
                if (initialized is not InvocationExpression { Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get }) continue;
                var method = loop.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression);
                if (method is null || temporary is not null && method.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == temporary.Identifier) != 1) continue;
                var allowed = loop.Descendants.OfType<IdentifierExpression>().Concat(removed.SelectMany(s => s.Descendants.OfType<IdentifierExpression>()))
                    .Concat(assignment.Descendants.OfType<IdentifierExpression>()).ToHashSet();
                if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == name && !allowed.Contains(id))) continue;
                var declarations = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == name)).ToArray();
                if (declarations is not [var declaration] || declaration.Variables.Count != 1
                    || declaration.Variables.Single().Initializer is not DefaultValueExpression) continue;
                var replacement = (BlockStatement)body.Clone();
                replacement.Statements.First().Remove();
                replacement.Statements.Last().Remove();
                loop.ReplaceWith(new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(current.Variables.Single().Name), get.Target.Clone(), replacement));
                foreach (var statement in removed) statement.Remove();
                assignment.Remove(); factory?.Remove(); declaration.Remove();
                foreach (var unused in method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Count == 1
                    && d.Variables.Single().Initializer is null && !method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == d.Variables.Single().Name)).ToArray()) unused.Remove();
            }
            RecoverAsyncLoops(rootNode);
        }
    }
}
