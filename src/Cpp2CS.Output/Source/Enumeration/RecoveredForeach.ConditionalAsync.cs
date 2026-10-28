using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    // 集合判空和 List.Count 不抛异常；把有条件的初始化视图交给既有异步清理规则。
    private static void RecoverConditionalAsyncLoops(AstNode root)
    {
        foreach (var method in root.Descendants.OfType<MethodDeclaration>().ToArray())
        {
            if (!method.Modifiers.HasFlag(Modifiers.Async) || method.Body is not { } outer
                || outer.Statements.OfType<TryCatchStatement>().ToArray() is not [var guarded]
                || guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || catcher.Body?.Statements.ToArray() is not [IfElseStatement { FalseStatement: null,
                    Condition: UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: IdentifierExpression flag },
                    TrueStatement: BlockStatement { Statements.Count: 1 } rejected }, var saved, GotoStatement failed]
                || rejected.Statements.Single() is not ThrowStatement { Expression: null }
                || saved is not ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression pending } }
                || !Set(saved, pending.Identifier, catcher.VariableName)
                || guarded.TryBlock?.Statements.ToArray() is not [var disabled, var enabled, VariableDeclarationStatement source,
                    IfElseStatement { FalseStatement: null, TrueStatement: BlockStatement branch } choice]
                || !Flag(disabled, flag.Identifier, false) || !Flag(enabled, flag.Identifier, true)
                || source.Variables.ToArray() is not [var collection]
                || choice.Condition is not BinaryOperatorExpression { Operator: BinaryOperatorType.ConditionalAnd,
                    Left: var present, Right: BinaryOperatorExpression { Left: MemberReferenceExpression { MemberName: "Count", Target: var receiver } count,
                        Right: var threshold } size }
                || !NullTest(present, collection.Name, BinaryOperatorType.InEquality) || !Name(receiver, collection.Name)
                || !(size.Operator == BinaryOperatorType.GreaterThanOrEqual && IntegerConstant(threshold, 1)
                    || size.Operator == BinaryOperatorType.GreaterThan && IntegerConstant(threshold, 0))
                || count.GetSymbol() is not IProperty { DeclaringType: var owner }
                || owner.GetDefinition() is not { ReflectionName: "System.Collections.Generic.List`1", ParentModule.AssemblyName: "mscorlib" or "System.Private.CoreLib" }
                || branch.Statements.ToArray() is not [var uninitialized, VariableDeclarationStatement factory, var initialized, var copied,
                    WhileStatement loop, GotoStatement normal]
                || !Flag(uninitialized, flag.Identifier, false) || !Flag(initialized, flag.Identifier, true)
                || factory.Variables.ToArray() is not [{ Initializer: InvocationExpression { Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "GetEnumerator", Target: var items } } invocation } created]
                || !Name(items, collection.Name) || Enumerator(invocation).Reference != false
                || copied is not ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression iterator } }
                || !Set(copied, iterator.Identifier, created.Name)) continue;
            var safeSource = collection.Initializer is IdentifierExpression id && (id.GetSymbol() is IField { IsStatic: false }
                    || method.Parameters.Any(p => p.Name == id.Identifier))
                || collection.Initializer is MemberReferenceExpression { Target: ThisReferenceExpression } field && field.GetSymbol() is IField { IsStatic: false };
            if (!safeSource) continue;
            var tail = outer.Statements.SkipWhile(s => s != guarded).Skip(1).Where(s => s is not EmptyStatement).ToArray();
            if (tail is not [GotoStatement skip, LabelStatement success, var empty, GotoStatement normalCleanup,
                    LabelStatement cleanup, var dispose, VariableDeclarationStatement exception, IfElseStatement thrown, var reset,
                    GotoStatement finished, LabelStatement end]
                || normal.Label != success.Label || failed.Label != cleanup.Label || normalCleanup.Label != cleanup.Label
                || skip.Label != end.Label || finished.Label != end.Label || !Set(empty, pending.Identifier, null)
                || !Dispose(dispose, iterator.Identifier) || exception.Variables.ToArray() is not [var alias]
                || !Name(alias.Initializer, pending.Identifier) || !NullTest(thrown.Condition, alias.Name, BinaryOperatorType.InEquality)
                || thrown.FalseStatement is not null || thrown.TrueStatement is not BlockStatement { Statements.Count: 1 } throwing
                || throwing.Statements.Single() is not ThrowStatement { Expression: var error } || !Name(error, alias.Name)
                || reset is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                    Left: var resetTarget, Right: DefaultValueExpression } } || !Name(resetTarget, iterator.Identifier)) continue;

            var view = (MethodDeclaration)method.Clone();
            var canonical = new BlockStatement();
            foreach (var declaration in outer.Statements.TakeWhile(s => s != guarded)) canonical.Statements.Add(declaration.Clone());
            var inner = (TryCatchStatement)guarded.Clone();
            inner.TryBlock = new BlockStatement();
            foreach (var statement in branch.Statements.TakeWhile(s => s != normal)) inner.TryBlock.Statements.Add(statement.Clone());
            canonical.Statements.Add(inner);
            canonical.Statements.Add(empty.Clone()); canonical.Statements.Add(normalCleanup.Clone());
            canonical.Statements.Add(cleanup.Clone()); canonical.Statements.Add(dispose.Clone()); canonical.Statements.Add(exception.Clone());
            canonical.Statements.Add(new IfElseStatement(new BinaryOperatorExpression(new IdentifierExpression(alias.Name), BinaryOperatorType.Equality,
                new NullReferenceExpression()), new BlockStatement { reset.Clone(), new ReturnStatement() }));
            canonical.Statements.Add(throwing.Statements.Single().Clone());
            view.Body = canonical;
            var tree = new SyntaxTree(); var type = new TypeDeclaration { Name = "EnumerationView" };
            type.Members.Add(view); tree.Members.Add(type);
            RecoverGuardedAsyncLoops(tree);
            if (ReferenceEquals(view.Body, canonical)) continue;
            var replacement = new BlockStatement { source.Clone(), new IfElseStatement(choice.Condition.Clone(), view.Body!.Clone()) };
            method.Body = replacement;
        }
    }
}
