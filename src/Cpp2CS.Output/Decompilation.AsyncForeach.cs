using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private sealed partial class RecoveredForeach
    {
        private static bool Flag(Statement statement, string name, bool? value = null) => statement is ExpressionStatement
            { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var left, Right: PrimitiveExpression { Value: bool actual } } }
            && Name(left, name) && (value is null || value == actual);

        // async 提升后，原生 EH 的启用标志仍把枚举器初始化与循环放在同一 catch 中。
        private static void RecoverAsyncLoops(AstNode root)
        {
            foreach (var method in root.Descendants.OfType<MethodDeclaration>().ToArray())
            {
                if (method.Body is not { } outer || outer.Statements.OfType<TryCatchStatement>().ToArray() is not [var guarded]
                    || guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                    || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                    || catcher.Body?.Statements.ToArray() is not [var save, IfElseStatement test, ThrowStatement { Expression: null }]
                    || save is not ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression saved } }
                    || !Set(save, saved.Identifier, catcher.VariableName) || test.Condition is not IdentifierExpression flag
                    || test.FalseStatement is not null || test.TrueStatement is not BlockStatement { Statements.Count: 1 } conditional
                    || conditional.Statements.Single() is not GotoStatement failure
                    || guarded.TryBlock is not { } tryBody || tryBody.Statements.OfType<IfElseStatement>().ToArray() is not [var selection]
                    || selection.FalseStatement is not null || selection.TrueStatement is not BlockStatement selected) continue;
                var contents = selected.Statements.ToArray();
                var loops = contents.OfType<WhileStatement>().ToArray();
                if (loops is not [var loop] || loop.Condition is not InvocationExpression { Arguments.Count: 0,
                        Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }
                    || loop.EmbeddedStatement is not BlockStatement body || body.Statements.FirstOrDefault() is not VariableDeclarationStatement current
                    || current.Variables.ToArray() is not [var element]
                    || element.Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var receiver }
                    || !Name(receiver, enumerator.Identifier) || body.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == enumerator.Identifier) != 1
                    || contents.SkipWhile(s => s != loop).Skip(1).ToArray() is not [GotoStatement success]) continue;
                var prefix = contents.TakeWhile(s => s != loop).ToArray();
                if (prefix.Length < 3 || !Flag(prefix[0], flag.Identifier, false)
                    || prefix[1] is not VariableDeclarationStatement factory || factory.Variables.ToArray() is not [var created]
                    || created.Initializer is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get }
                    || created.Initializer.Annotation<ResolveResult>()?.Type.GetAllBaseTypes().Any(t => t.FullName == "System.IDisposable") != true
                    || !Flag(prefix[2], flag.Identifier, true)) continue;
                var copied = new HashSet<string> { created.Name };
                var valid = true;
                foreach (var statement in prefix.Skip(3))
                {
                    if (statement is ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                            Left: IdentifierExpression destination, Right: IdentifierExpression source } } && copied.Contains(source.Identifier)) copied.Add(destination.Identifier);
                    else if (statement is VariableDeclarationStatement declaration && declaration.Variables.ToArray() is [var variable]
                        && variable.Initializer is IdentifierExpression from && copied.Contains(from.Identifier)) copied.Add(variable.Name);
                    else valid = false;
                }
                if (!valid || !copied.Contains(enumerator.Identifier)) continue;
                var tail = outer.Statements.SkipWhile(s => s != guarded).Skip(1).Where(s => s is not EmptyStatement).ToArray();
                if (tail is not [GotoStatement skip, LabelStatement normal, VariableDeclarationStatement empty, GotoStatement normalJoin,
                    LabelStatement failed, var copy, GotoStatement failedJoin, LabelStatement cleanup, var dispose,
                    VariableDeclarationStatement exception, IfElseStatement rethrow, var reset, GotoStatement finish, LabelStatement end]
                    || normal.Label != success.Label || failed.Label != failure.Label || skip.Label != end.Label || finish.Label != end.Label
                    || normalJoin.Label != cleanup.Label || failedJoin.Label != cleanup.Label
                    || empty.Variables.ToArray() is not [var merged] || merged.Initializer is not NullReferenceExpression
                    || !Set(copy, merged.Name, saved.Identifier) || !Dispose(dispose, enumerator.Identifier)
                    || exception.Variables.ToArray() is not [var thrown] || !Name(thrown.Initializer, merged.Name)
                    || !NullTest(rethrow.Condition, thrown.Name, BinaryOperatorType.InEquality) || rethrow.FalseStatement is not null
                    || rethrow.TrueStatement is not BlockStatement { Statements.Count: 1 } throwBlock
                    || throwBlock.Statements.Single() is not ThrowStatement throwStatement || !Name(throwStatement.Expression, thrown.Name)
                    || reset is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                        Left: var resetTarget, Right: DefaultValueExpression } } || !Name(resetTarget, enumerator.Identifier)) continue;
                var before = tryBody.Statements.TakeWhile(s => s != selection).Where(s => !Flag(s, flag.Identifier)).ToArray();
                if (tryBody.Statements.Last() != selection || before is not [VariableDeclarationStatement listDeclaration]
                    || listDeclaration.Variables.ToArray() is not [var list] || list.Initializer is not (IdentifierExpression or MemberReferenceExpression { Target: ThisReferenceExpression })
                    || !Name(get.Target, list.Name)
                    || selection.Condition is not BinaryOperatorExpression { Operator: BinaryOperatorType.ConditionalAnd,
                        Left: var nonnull, Right: BinaryOperatorExpression { Operator: BinaryOperatorType.GreaterThanOrEqual,
                            Left: MemberReferenceExpression { MemberName: "Count", Target: var countReceiver }, Right: PrimitiveExpression { Value: 1 } } }
                    || !NullTest(nonnull, list.Name, BinaryOperatorType.InEquality) || !Name(countReceiver, list.Name)) continue;
                var scaffolding = new HashSet<string> { flag.Identifier, saved.Identifier, enumerator.Identifier };
                if (outer.Statements.TakeWhile(s => s != guarded).Any(s => s is not VariableDeclarationStatement d
                    || d.Variables.Any(v => !scaffolding.Contains(v.Name) || v.Initializer is not (null or DefaultValueExpression)))) continue;
                // 跳转和标志仅服务于此清理模板，循环体不得引用它们。
                var internalNames = copied.Concat([flag.Identifier, saved.Identifier, merged.Name, thrown.Name]).ToHashSet();
                if (body.Descendants.OfType<IdentifierExpression>().Any(id => internalNames.Contains(id.Identifier) && id.Identifier != enumerator.Identifier)) continue;
                var labels = body.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
                if (body.Descendants.OfType<GotoStatement>().Any(jump => jump.Label is null || !labels.Contains(jump.Label))) continue;
                var content = (BlockStatement)body.Clone();
                content.Statements.First().Remove();
                var restored = (IfElseStatement)selection.Clone();
                restored.TrueStatement = new BlockStatement { new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(element.Name), get.Target.Clone(), content) };
                method.Body = new BlockStatement { listDeclaration.Clone(), restored };
            }
        }
    }
}
