using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private sealed partial class RecoveredForeach
    {
        // 初始化成功标志只决定异常时是否清理；成功后的循环与正常后续工作保持原求值顺序。
        private static void RecoverGuardedAsyncLoops(AstNode root)
        {
            foreach (var method in root.Descendants.OfType<MethodDeclaration>().ToArray())
            {
                if (!method.Modifiers.HasFlag(Modifiers.Async) || method.Body is not { } outer
                    || outer.Statements.OfType<TryCatchStatement>().ToArray() is not [var guarded]
                    || guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                    || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                    || catcher.Body?.Statements.ToArray() is not [IfElseStatement
                        { Condition: UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: IdentifierExpression flag },
                            FalseStatement: null, TrueStatement: BlockStatement { Statements.Count: 1 } failed }, var saved, GotoStatement cleanupJump]
                    || failed.Statements.Single() is not ThrowStatement { Expression: null }
                    || saved is not ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression merged } }
                    || !Set(saved, merged.Identifier, catcher.VariableName) || guarded.TryBlock is not { } tryBody
                    || tryBody.Statements.LastOrDefault() is not WhileStatement { Condition: InvocationExpression { Arguments.Count: 0,
                        Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }, EmbeddedStatement: BlockStatement content } loop
                    || content.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.ToArray() is not [var element]
                    || element.Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var receiver } read
                    || !Name(receiver, enumerator.Identifier) || read.GetSymbol() is IProperty { ReturnType: ByReferenceType }
                    || content.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == enumerator.Identifier) != 1) continue;
                var prefix = tryBody.Statements.TakeWhile(s => s != loop).ToArray();
                var factories = prefix.OfType<VariableDeclarationStatement>().Where(d => d.Variables.ToArray() is
                    [{ Initializer: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } } }]).ToArray();
                if (factories is not [var factory]) continue;
                var created = factory.Variables.Single();
                var invocation = (InvocationExpression)created.Initializer!;
                var get = (MemberReferenceExpression)invocation.Target;
                if (invocation.Annotation<ResolveResult>()?.Type.GetAllBaseTypes().Any(t => t.FullName == "System.IDisposable") != true) continue;
                var before = prefix.TakeWhile(s => s != factory).ToArray();
                if (before.LastOrDefault(s => Flag(s, flag.Identifier)) is not { } disabled || !Flag(disabled, flag.Identifier, false)) continue;
                bool Pure(Expression? value) => value is DefaultValueExpression or NullReferenceExpression or PrimitiveExpression or ThisReferenceExpression
                    || value is IdentifierExpression id && (id.GetSymbol() is IField { IsStatic: false }
                        || before.OfType<VariableDeclarationStatement>().Any(d => d.Variables.Any(v => v.Name == id.Identifier))
                        || method.Parameters.Any(p => p.Name == id.Identifier))
                    || value is MemberReferenceExpression { Target: ThisReferenceExpression } member && member.GetSymbol() is IField { IsStatic: false };
                if (before.Any(s => !Flag(s, flag.Identifier) && (s is not VariableDeclarationStatement declaration
                        || declaration.Variables.Any(v => !Pure(v.Initializer))))) continue;
                var after = prefix.SkipWhile(s => s != factory).Skip(1).ToArray();
                if (after.FirstOrDefault() is not { } enabled || !Flag(enabled, flag.Identifier, true)) continue;
                var copied = new HashSet<string> { created.Name };
                var valid = true;
                foreach (var statement in after.Skip(1))
                    if (statement is ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                            Left: IdentifierExpression target, Right: IdentifierExpression source } } && copied.Contains(source.Identifier)) copied.Add(target.Identifier);
                    else valid = false;
                if (!valid || !copied.Contains(enumerator.Identifier)) continue;
                var tail = outer.Statements.SkipWhile(s => s != guarded).Skip(1).ToArray();
                if (tail is not [var empty, GotoStatement normalJump, LabelStatement cleanup, var dispose,
                    VariableDeclarationStatement exception, IfElseStatement success, ThrowStatement thrown]
                    || !Set(empty, merged.Identifier, null) || cleanupJump.Label != cleanup.Label || normalJump.Label != cleanup.Label
                    || !Dispose(dispose, enumerator.Identifier) || exception.Variables.ToArray() is not [var alias]
                    || !Name(alias.Initializer, merged.Identifier) || !NullTest(success.Condition, alias.Name, BinaryOperatorType.Equality)
                    || success.FalseStatement is not null || success.TrueStatement is not BlockStatement continuation
                    || !Name(thrown.Expression, alias.Name) || continuation.Statements.FirstOrDefault() is not ExpressionStatement
                        { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var reset, Right: DefaultValueExpression } }
                    || !Name(reset, enumerator.Identifier)) continue;
                var internalNames = copied.Concat([flag.Identifier, merged.Identifier, alias.Name]).ToHashSet();
                if (outer.Statements.TakeWhile(s => s != guarded).Any(s => s is not VariableDeclarationStatement d
                        || d.Variables.Any(v => !internalNames.Contains(v.Name) || v.Initializer is not (null or DefaultValueExpression)))
                    || content.Descendants.OfType<IdentifierExpression>().Any(id => internalNames.Contains(id.Identifier) && id.Identifier != enumerator.Identifier)
                    || before.Where(s => !Flag(s, flag.Identifier)).SelectMany(s => s.Descendants.OfType<IdentifierExpression>()).Any(id => internalNames.Contains(id.Identifier))
                    || get.Target.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => internalNames.Contains(id.Identifier))
                    || continuation.Statements.Skip(1).SelectMany(s => s.Descendants.OfType<IdentifierExpression>()).Any(id => internalNames.Contains(id.Identifier))) continue;
                bool UsesCurrent(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => id.Identifier == element.Name);
                if (content.Descendants.OfType<AssignmentExpression>().Any(a => UsesCurrent(a.Left))
                    || content.Descendants.OfType<DirectionExpression>().Any(d => UsesCurrent(d.Expression))
                    || content.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                        or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && UsesCurrent(u.Expression))) continue;
                var labels = content.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
                if (content.Descendants.OfType<GotoStatement>().Any(jump => jump.Label is null || !labels.Contains(jump.Label))) continue;
                var body = (BlockStatement)content.Clone();
                body.Statements.First().Remove();
                var replacement = new BlockStatement();
                foreach (var statement in before.Where(s => !Flag(s, flag.Identifier))) replacement.Statements.Add(statement.Clone());
                replacement.Statements.Add(new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(element.Name), get.Target.Clone(), body));
                foreach (var statement in continuation.Statements.Skip(1)) replacement.Statements.Add(statement.Clone());
                foreach (var declaration in replacement.Statements.OfType<VariableDeclarationStatement>().ToArray())
                    if (declaration.Variables.ToArray() is [{ Initializer: DefaultValueExpression } unused]
                        && !replacement.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == unused.Name)) declaration.Remove();
                if (replacement.Statements.LastOrDefault() is ReturnStatement { Expression: null } last) last.Remove();
                method.Body = replacement;
            }
        }
    }
}
