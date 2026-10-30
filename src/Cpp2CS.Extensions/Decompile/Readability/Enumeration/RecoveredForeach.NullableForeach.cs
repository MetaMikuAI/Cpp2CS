using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;

namespace Cpp2CS.Extensions.Decompile;

internal sealed partial class RecoveredForeach
{
    private static bool NullableDispose(Statement statement, string name)
    {
        if (statement is not ExpressionStatement expression) return false;
        var value = expression.Expression;
        if (value is UnaryOperatorExpression { Operator: UnaryOperatorType.NullConditionalRewrap } wrap) value = wrap.Expression;
        return value is InvocationExpression
        {
            Arguments.Count: 0, Target: MemberReferenceExpression
            {
                MemberName: "Dispose",
                Target: UnaryOperatorExpression { Operator: UnaryOperatorType.NullConditional, Expression: var receiver }
            }
        } && Name(receiver, name);
    }

    // 引用枚举器的共享条件清理；循环前只允许无副作用的局部初始化。
    private static void RecoverNullableMergedLoops(AstNode root)
    {
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().Reverse().ToArray())
        {
            if (guarded.Parent is not BlockStatement parent || guarded.FinallyBlock is not null
                || guarded.CatchClauses.ToArray() is not [var catcher] || catcher.Condition is not null
                || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || catcher.Body?.Statements.ToArray() is not [var saved, GotoStatement failure]
                || saved is not ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression pending } }
                || !Set(saved, pending.Identifier, catcher.VariableName)
                || guarded.TryBlock?.Statements.LastOrDefault() is not WhileStatement
                {
                    Condition: InvocationExpression
                    {
                        Arguments.Count: 0, Target: MemberReferenceExpression
                        {
                            MemberName: "MoveNext",
                            Target: IdentifierExpression enumerator
                        }
                    }, EmbeddedStatement: BlockStatement body
                }
                || body.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.ToArray() is not [var element]
                || element.Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var receiver } read
                || !Name(receiver, enumerator.Identifier) || CurrentByReference(read)) continue;
            var prefix = guarded.TryBlock.Statements.Take(guarded.TryBlock.Statements.Count - 1).ToArray();
            if (prefix.FirstOrDefault() is not IfElseStatement guard || !NullTest(guard.Condition, enumerator.Identifier, BinaryOperatorType.Equality)
                || guard.FalseStatement is not null || guard.TrueStatement is not BlockStatement { Statements.Count: 1 } missing
                || missing.Statements.Single() is not ThrowStatement { Expression: ObjectCreateExpression { Arguments.Count: 0 } error }
                || error.Type?.ToString() is not ("NullReferenceException" or "System.NullReferenceException")
                || prefix.Skip(1).Any(s => s is not VariableDeclarationStatement d || d.Variables.Any(v => v.Initializer is not
                    (IdentifierExpression or PrimitiveExpression or NullReferenceExpression or DefaultValueExpression)))) continue;
            var statements = parent.Statements.ToArray(); var index = Array.IndexOf(statements, guarded);
            if (index < 2 || statements[index - 2] is not VariableDeclarationStatement factory || factory.Variables.ToArray() is not [var created]
                || created.Name != enumerator.Identifier || created.Initializer is not InvocationExpression
                {
                    Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get
                } invocation
                || invocation.Annotation<ResolveResult>()?.Type is not { IsReferenceType: true } enumeratorType
                || !Enumerator(enumeratorType).Disposable
                || statements[index - 1] is not VariableDeclarationStatement exception || exception.Variables.ToArray() is not [{ Initializer: null } merged]
                || merged.Name != pending.Identifier) continue;
            if (statements.Skip(index + 1).Take(6).ToArray() is not [var empty, GotoStatement success, LabelStatement cleanup,
                    var dispose, IfElseStatement continuation, ThrowStatement rethrow]
                || !Set(empty, pending.Identifier, null) || failure.Label != cleanup.Label || success.Label != cleanup.Label
                || !NullableDispose(dispose, enumerator.Identifier) || continuation.FalseStatement is not null
                || continuation.TrueStatement is not BlockStatement after || !NullTest(continuation.Condition, pending.Identifier, BinaryOperatorType.Equality)
                || !Name(rethrow.Expression, pending.Identifier)) continue;
            var method = guarded.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression);
            if (method is null) continue;
            var copiedNames = prefix.Skip(1).SelectMany(s => s.Descendants.OfType<IdentifierExpression>()).Select(id => id.Identifier).ToHashSet();
            var locals = method.Descendants.OfType<VariableInitializer>().Select(v => v.Name)
                .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
            bool ReadsCopied(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => copiedNames.Contains(id.Identifier));
            // 初始化移到 foreach 前；工厂求值不能改写其读取的局部。
            if (!copiedNames.All(locals.Contains)
                || method.Descendants.Where(n => n is DirectionExpression or LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement).Any(ReadsCopied)
                || invocation.Descendants.OfType<AssignmentExpression>().Any(a => ReadsCopied(a.Left))
                || invocation.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                    or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && ReadsCopied(u.Expression))) continue;
            var allowedException = saved.Descendants.Concat(empty.Descendants).Concat(continuation.Condition!.DescendantsAndSelf).Concat(rethrow.Descendants).ToHashSet();
            var allowedEnum = guard.Descendants.Concat(((WhileStatement)guarded.TryBlock.Statements.Last()).Condition!.DescendantsAndSelf)
                .Concat(read.Descendants).Concat(dispose.Descendants).ToHashSet();
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == pending.Identifier && !allowedException.Contains(id)
                || id.Identifier == enumerator.Identifier && !allowedEnum.Contains(id))
                || method.Descendants.OfType<GotoStatement>().Any(j => j.Label == cleanup.Label && j != failure && j != success)) continue;
            var labels = body.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            if (body.Descendants.OfType<ReturnStatement>().Any()
                || body.Descendants.OfType<GotoStatement>().Any(j => j.Label is null || !labels.Contains(j.Label))
                || method.Descendants.OfType<GotoStatement>().Any(j => j.Label is not null && labels.Contains(j.Label) && !body.Descendants.Contains(j))) continue;
            bool UsesElement(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => id.Identifier == element.Name);
            if (body.Descendants.OfType<AssignmentExpression>().Any(a => UsesElement(a.Left))
                || body.Descendants.OfType<DirectionExpression>().Any(d => UsesElement(d.Expression))
                || body.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                    or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && UsesElement(u.Expression))) continue;
            var content = (BlockStatement)body.Clone(); content.Statements.First().Remove();
            var replacement = new BlockStatement();
            foreach (var statement in prefix.Skip(1)) replacement.Statements.Add(statement.Clone());
            replacement.Statements.Add(new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(element.Name), get.Target.Clone(), content));
            guarded.ReplaceWith(replacement);
            continuation.ReplaceWith(after.Clone());
            foreach (var statement in statements.Skip(index - 2).Take(9).Where(s => s != guarded && s != continuation)) statement.Remove();
        }
    }
}
