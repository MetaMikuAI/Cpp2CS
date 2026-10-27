using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private sealed partial class RecoveredForeach
    {
        // 正常路径和异常路径共用 Dispose；合流值只允许用于随后的重抛。
        private static void RecoverMergedLoops(AstNode root)
        {
            foreach (var block in root.Descendants.OfType<BlockStatement>().ToArray())
            foreach (var guarded in block.Statements.OfType<TryCatchStatement>().ToArray())
            {
                if (guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                    || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                    || catcher.Body?.Statements.ToArray() is not [var saved, GotoStatement failure]
                    || saved is not ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression merged } }
                    || !Set(saved, merged.Identifier, catcher.VariableName)
                    || guarded.TryBlock?.Statements.ToArray() is not [WhileStatement { Condition: InvocationExpression { Arguments.Count: 0,
                        Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }, EmbeddedStatement: BlockStatement content }]
                    || content.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.ToArray() is not [var element]
                    || element.Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var receiver } read
                    || !Name(receiver, enumerator.Identifier) || read.GetSymbol() is IProperty { ReturnType: ByReferenceType }
                    || content.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == enumerator.Identifier) != 1) continue;
                var statements = block.Statements.ToArray();
                var index = Array.IndexOf(statements, guarded);
                if (index < 2 || statements[index - 2] is not VariableDeclarationStatement factory || factory.Variables.ToArray() is not [var created]
                    || created.Name != enumerator.Identifier || created.Initializer is not InvocationExpression { Arguments.Count: 0,
                        Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get } invocation
                    || invocation.Annotation<ResolveResult>()?.Type.GetAllBaseTypes().Any(t => t.FullName == "System.IDisposable") != true
                    || statements[index - 1] is not VariableDeclarationStatement pending || pending.Variables.ToArray() is not [{ Initializer: null } pendingValue]
                    || pendingValue.Name != merged.Identifier) continue;
                if (statements.Skip(index + 1).Take(7).ToArray() is not [var empty, GotoStatement success, LabelStatement cleanup, var dispose,
                        VariableDeclarationStatement exception, IfElseStatement rethrow, var reset]
                    || !Set(empty, merged.Identifier, null) || failure.Label != cleanup.Label || success.Label != cleanup.Label
                    || !Dispose(dispose, enumerator.Identifier) || exception.Variables.ToArray() is not [var alias]
                    || !Name(alias.Initializer, merged.Identifier) || !NullTest(rethrow.Condition, alias.Name, BinaryOperatorType.InEquality)
                    || rethrow.FalseStatement is not null || rethrow.TrueStatement is not BlockStatement { Statements.Count: 1 } throwBody
                    || throwBody.Statements.Single() is not ThrowStatement thrown || !Name(thrown.Expression, alias.Name)
                    || reset is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                        Left: var resetTarget, Right: DefaultValueExpression } } || !Name(resetTarget, enumerator.Identifier)) continue;
                var method = guarded.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression);
                if (method is null) continue;
                var removed = statements.Skip(index - 2).Take(10).ToArray();
                var allowed = removed.SelectMany(s => s.DescendantsAndSelf).ToHashSet();
                var internalNames = new HashSet<string> { enumerator.Identifier, merged.Identifier, alias.Name };
                if (method.Descendants.OfType<IdentifierExpression>().Any(id => internalNames.Contains(id.Identifier) && !allowed.Contains(id))
                    || content.Descendants.OfType<IdentifierExpression>().Any(id => internalNames.Contains(id.Identifier) && id.Identifier != enumerator.Identifier)
                    || method.Descendants.OfType<GotoStatement>().Any(j => j.Label == cleanup.Label && j != failure && j != success)) continue;
                var labels = content.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
                if (content.Descendants.OfType<GotoStatement>().Any(j => j.Label is null || !labels.Contains(j.Label))
                    || method.Descendants.OfType<GotoStatement>().Any(j => j.Label is not null && labels.Contains(j.Label) && !content.Descendants.Contains(j))) continue;
                var body = (BlockStatement)content.Clone();
                var item = element.Name;
                bool UsesElement(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => id.Identifier == element.Name);
                var writable = content.Descendants.OfType<AssignmentExpression>().Any(a => UsesElement(a.Left))
                    || content.Descendants.OfType<DirectionExpression>().Any(d => UsesElement(d.Expression))
                    || content.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                        or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && UsesElement(u.Expression));
                if (writable)
                {
                    var names = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                        .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name))
                        .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
                    item = "item";
                    for (var suffix = 2; names.Contains(item); suffix++) item = "item" + suffix;
                    ((VariableDeclarationStatement)body.Statements.First()).Variables.Single().Initializer = new IdentifierExpression(item);
                }
                else body.Statements.First().Remove();
                guarded.ReplaceWith(new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(item), get.Target.Clone(), body));
                foreach (var statement in removed.Where(s => s != guarded)) statement.Remove();
            }
        }
    }
}
