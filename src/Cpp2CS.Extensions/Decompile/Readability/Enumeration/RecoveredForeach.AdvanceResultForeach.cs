using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;

namespace Cpp2CS.Extensions.Decompile;

internal sealed partial class RecoveredForeach
{
    // MoveNext 的零/一结果只沿耗尽和提前退出两条路径传到清理之后。
    private static void RecoverAdvanceResultLoops(AstNode root)
    {
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().Reverse().ToArray())
        {
            if (guarded.Parent is not BlockStatement parent || guarded.Ancestors.OfType<CheckedStatement>().Any()
                || guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || guarded.TryBlock is not { } tryBody || tryBody.Statements.Count < 2
                || tryBody.Statements.OfType<WhileStatement>().ToArray() is not [
                { Condition: PrimitiveExpression { Value: true }, EmbeddedStatement: BlockStatement content } loop]
                || content.Statements.ToArray() is not [VariableDeclarationStatement advance, VariableDeclarationStatement carried,
                    IfElseStatement { FalseStatement: null, TrueStatement: BlockStatement positive } test,
                    ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var exhaustedTarget, Right: var exhaustedValue } }, BreakStatement]
                || exhaustedTarget is not IdentifierExpression state || !IntegerConstant(exhaustedValue, 0)
                || advance.Variables.ToArray() is not [var flag] || !Name(test.Condition, flag.Name)
                || flag.Initializer is not InvocationExpression
                {
                    Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator }
                }
                || carried.Variables.ToArray() is not [var carriedValue]
                || carriedValue.Initializer is not ConditionalExpression { Condition: var condition, TrueExpression: var one, FalseExpression: var zero }
                || !Name(condition, flag.Name) || !IntegerConstant(one, 1) || !IntegerConstant(zero, 0)
                || positive.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.ToArray() is not [var element]
                || element.Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var receiver } read
                || !Name(receiver, enumerator.Identifier) || CurrentByReference(read)
                || positive.Statements.TakeLast(2).ToArray() is not [ExpressionStatement
                {
                    Expression: AssignmentExpression
                    {
                        Operator: AssignmentOperatorType.Assign,
                        Left: var foundTarget, Right: var foundValue
                    }
                }, BreakStatement stopped]
                || !Name(foundTarget, state.Identifier) || !Name(foundValue, carriedValue.Name)
                || !ConditionalCleanup(catcher, enumerator.Identifier)) continue;
            var suffix = tryBody.Statements.SkipWhile(s => s != loop).Skip(1).ToArray();
            bool Copy(Statement statement) => PureLocals(statement) || statement is ExpressionStatement
            {
                Expression: AssignmentExpression
                {
                    Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression,
                    Right: IdentifierExpression or PrimitiveExpression
                }
            };
            if (suffix.Any(s => !Copy(s)) || suffix.OfType<ExpressionStatement>().Where(s => s.Expression is AssignmentExpression assignment
                    && Name(assignment.Right, state.Identifier)).ToArray() is not [var transfer]
                || transfer.Expression is not AssignmentExpression { Left: IdentifierExpression output }) continue;
            var siblings = parent.Statements.ToArray(); var index = Array.IndexOf(siblings, guarded);
            if (index + 1 >= siblings.Length || !Dispose(siblings[index + 1], enumerator.Identifier)) continue;
            var factory = siblings.Take(index).OfType<VariableDeclarationStatement>().LastOrDefault(d => d.Variables.Any(v => v.Name == enumerator.Identifier));
            if (factory?.Variables.ToArray() is not [var initialized] || initialized.Initializer is not InvocationExpression
                {
                    Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get
                } invocation
                || !Enumerator(invocation).Disposable
                || guarded.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is not { } method) continue;
            var before = tryBody.Statements.TakeWhile(s => s != loop).ToArray();
            if (before.FirstOrDefault() is not IfElseStatement guard || !NullTest(guard.Condition, enumerator.Identifier, BinaryOperatorType.Equality)
                || guard.FalseStatement is not null || guard.TrueStatement is not BlockStatement { Statements.Count: 1 } missing
                || missing.Statements.Single() is not ThrowStatement { Expression: ObjectCreateExpression { Arguments.Count: 0 } error }
                || error.Type?.ToString() is not ("NullReferenceException" or "System.NullReferenceException")) continue;
            var prefix = before.Skip(1).Where(s => s is not VariableDeclarationStatement d || d.Variables.ToArray() is not [{ Initializer: null } v] || v.Name != state.Identifier).ToArray();
            if (before.OfType<VariableDeclarationStatement>().SelectMany(d => d.Variables).Count(v => v.Name == state.Identifier && v.Initializer is null) != 1
                || prefix.Any(s => !Copy(s))) continue;
            var outside = siblings.Skip(Array.IndexOf(siblings, factory) + 1).Take(index - Array.IndexOf(siblings, factory) - 1).ToArray();
            var numeric = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Type is PrimitiveType
            {
                Keyword:
                "byte" or "sbyte" or "short" or "ushort" or "int" or "uint" or "long" or "ulong" or "float" or "double"
            }).SelectMany(d => d.Variables).Select(v => v.Name).ToHashSet();
            bool Scalar(Expression? value) => value is PrimitiveExpression || value is IdentifierExpression id && numeric.Contains(id.Identifier)
                || value is ParenthesizedExpression parentheses && Scalar(parentheses.Expression!)
                || value is BinaryOperatorExpression
                {
                    Operator: BinaryOperatorType.Add or BinaryOperatorType.Subtract or BinaryOperatorType.Multiply
                    or BinaryOperatorType.BitwiseAnd or BinaryOperatorType.BitwiseOr or BinaryOperatorType.ExclusiveOr
                } binary && Scalar(binary.Left) && Scalar(binary.Right);
            if (outside.Any(s => !PureLocals(s) && (s is not VariableDeclarationStatement d || d.Variables.Any(v => v.Initializer is null || !Scalar(v.Initializer))))
                || !StableCopies(method, outside.Concat(prefix).Concat(suffix), invocation)) continue;
            var declarations = siblings.Take(index).OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == output.Identifier)).ToArray();
            if (declarations is not [var resultDeclaration] || resultDeclaration.Variables.ToArray() is not [{ Initializer: null } resultVariable]) continue;
            var after = siblings.Skip(index + 2).SelectMany(s => s.DescendantsAndSelf).ToHashSet();
            var internalNames = new[] { flag.Name, carriedValue.Name, state.Identifier };
            if (internalNames.Any(name => method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == name && !guarded.Descendants.Contains(id)))
                || content.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == flag.Name) != 2
                || content.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == carriedValue.Name) != 1
                || guarded.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == state.Identifier) != 3
                || method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == output.Identifier && id != output && !after.Contains(id))) continue;
            var allowed = guarded.Descendants.Concat(siblings[index + 1].Descendants).ToHashSet();
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == enumerator.Identifier && !allowed.Contains(id))
                || positive.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == enumerator.Identifier) != 1) continue;
            var written = prefix.Concat(suffix).OfType<ExpressionStatement>()
                .Select(s => ((IdentifierExpression)((AssignmentExpression)s.Expression).Left).Identifier).ToHashSet();
            if (guarded.Ancestors.OfType<TryCatchStatement>().SelectMany(t => t.CatchClauses.SelectMany(c => c.Descendants)
                .Concat(t.FinallyBlock?.Descendants ?? [])).OfType<IdentifierExpression>().Any(id => written.Contains(id.Identifier))) continue;
            var labels = positive.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            if (positive.Descendants.OfType<ReturnStatement>().Any()
                || positive.Descendants.OfType<GotoStatement>().Any(j => j.Label is null || !labels.Contains(j.Label))
                || method.Descendants.OfType<GotoStatement>().Any(j => j.Label is not null && labels.Contains(j.Label) && !positive.Descendants.Contains(j))
                || positive.Descendants.OfType<BreakStatement>().Any(b => b != stopped
                    && b.Ancestors.FirstOrDefault(n => n is WhileStatement or DoWhileStatement or ForStatement or ForeachStatement or SwitchStatement) == loop)) continue;
            bool UsesElement(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => id.Identifier == element.Name);
            bool Written(Expression expression) => UsesElement(expression) && (read.Annotation<ResolveResult>()?.Type.IsReferenceType != true || Name(expression, element.Name));
            if (positive.Descendants.OfType<AssignmentExpression>().Any(a => Written(a.Left))
                || positive.Descendants.OfType<DirectionExpression>().Any(d => UsesElement(d.Expression))
                || positive.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                    or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && Written(u.Expression))) continue;
            var body = (BlockStatement)positive.Clone(); body.Statements.First().Remove(); body.Statements.Last().Remove(); body.Statements.Last().Remove();
            body.Statements.Add(new ExpressionStatement(new AssignmentExpression(new IdentifierExpression(output.Identifier), one.Clone())));
            body.Statements.Add(new BreakStatement());
            var replacement = new BlockStatement(); foreach (var statement in prefix) replacement.Statements.Add(statement.Clone());
            replacement.Statements.Add(new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(element.Name), get.Target.Clone(), body));
            foreach (var statement in suffix.Where(s => s != transfer)) replacement.Statements.Add(statement.Clone());
            resultVariable.Initializer = zero.Clone();
            guarded.ReplaceWith(replacement); factory.Remove(); siblings[index + 1].Remove();
        }
    }
}
