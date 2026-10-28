using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

/// <summary>把枚举器的正常清理与捕获后清理配对，恢复 foreach 的隐式 finally。</summary>
internal sealed partial class RecoveredForeach : IAstTransform
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

    private static bool FirstReceiver(Expression? expression, Expression read) => ReferenceEquals(expression, read) || expression switch
    {
        InvocationExpression call => FirstReceiver(call.Target, read)
            || call.Target is IdentifierExpression && call.GetSymbol() is IMethod { DeclaringType.Kind: not TypeKind.Delegate }
                && FirstReceiver(call.Arguments.FirstOrDefault(), read),
        MemberReferenceExpression member => FirstReceiver(member.Target, read),
        IndexerExpression indexer => FirstReceiver(indexer.Target, read),
        ParenthesizedExpression parentheses => FirstReceiver(parentheses.Expression, read),
        UnaryOperatorExpression { Operator: UnaryOperatorType.NullConditional or UnaryOperatorType.NullConditionalRewrap } conditional
            => FirstReceiver(conditional.Expression, read),
        _ => false,
    };

    // 另一次 GetEnumerator 必须在同一块中先于使用，且没有可跳过初始化的标签。
    private static bool IndependentUse(IdentifierExpression use, string name, Statement removedInitialization, AstNode method)
    {
        bool Reset(Statement statement) => statement != removedInitialization && statement is ExpressionStatement
            { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var left,
                Right: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } } factory } }
            && Name(left, name) && !factory.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == name);
        if (use.Ancestors.TakeWhile(n => n != method).Any(n => n is EntityDeclaration or LambdaExpression or AnonymousMethodExpression)) return false;
        if (use.Parent is AssignmentExpression assignment && ReferenceEquals(assignment.Left, use)
            && assignment.Parent is Statement initialized && Reset(initialized)) return true;
        foreach (var anchor in use.Ancestors.OfType<Statement>())
        {
            if (anchor.Parent is not BlockStatement block) continue;
            foreach (var previous in block.Statements.TakeWhile(s => s != anchor).Reverse())
            {
                if (previous is LabelStatement || previous.DescendantsAndSelf.Any(n => n == removedInitialization)) return false;
                if (previous is ExpressionStatement { Expression: AssignmentExpression { Left: var left } } && Name(left, name)) return Reset(previous);
            }
        }
        return false;
    }

    public void Run(AstNode rootNode, TransformContext context)
    {
        var typedReads = NormalizeTypedCurrent(rootNode);
        RecoverSearchLoops(rootNode);
        var searches = NormalizeAdvanceSearch(rootNode);
        RecoverResultLoops(rootNode);
        foreach (var (original, replacement) in searches)
            if (replacement.Parent is not null) replacement.ReplaceWith(original);
        RecoverAdvanceResultLoops(rootNode);
        RecoverCompleteLoops(rootNode);
        var normalized = NormalizeDirectLoops(rootNode);
        foreach (var loop in rootNode.Descendants.OfType<WhileStatement>().ToArray())
        {
            if (loop.Parent is not BlockStatement parent || loop.Condition is not PrimitiveExpression { Value: true }
                || loop.EmbeddedStatement is not BlockStatement content) continue;
            var parts = content.Statements.ToArray();
            if (parts.OfType<TryCatchStatement>().ToArray() is not [var guarded]
                || guarded.FinallyBlock is not null || guarded.CatchClauses.Count != 1
                || guarded.TryBlock is not { } tryBlock) continue;
            var guardedStatements = tryBlock.Statements.ToArray();
            Expression? advance;
            BlockStatement body;
            var earlyExit = false;
            if (guardedStatements is [IfElseStatement { FalseStatement: null, TrueStatement: BlockStatement positive } test])
            { advance = test.Condition; body = positive; }
            else if (guardedStatements.FirstOrDefault() is IfElseStatement { FalseStatement: null,
                Condition: UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: var operand },
                TrueStatement: BlockStatement { Statements.Count: 1 } exited } && exited.Statements.Single() is BreakStatement)
            {
                advance = operand; earlyExit = true;
                body = new BlockStatement();
                foreach (var statement in guardedStatements.Skip(1)) body.Statements.Add(statement.Clone());
            }
            else continue;
            if (advance is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression
                    { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }
                || body.Statements.LastOrDefault() is not ContinueStatement) continue;
            var name = enumerator.Identifier;
            if (body.Descendants.OfType<MemberReferenceExpression>().Where(m => m.MemberName == "Current" && Name(m.Target, name)).ToArray()
                is not [var read]) continue;
            var current = body.Statements.FirstOrDefault() as VariableDeclarationStatement;
            if (current?.Variables.Count != 1 || !ReferenceEquals(current.Variables.Single().Initializer, read))
            {
                var first = body.Statements.FirstOrDefault() switch
                {
                    VariableDeclarationStatement { Variables.Count: 1 } firstDeclaration => firstDeclaration.Variables.Single().Initializer,
                    ExpressionStatement expression => expression.Expression,
                    _ => null,
                };
                if (!FirstReceiver(first, read) || CurrentByReference(read)) continue;
                current = null;
            }
            var catcher = guarded.CatchClauses.Single();
            if (catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || catcher.Body is not { } catchBody) continue;
            string? savedName = null;
            string? failureLabel = null;
            var mergedCatch = false;
            var directCatch = catchBody.Statements.ToArray() is [var catchCleanup, ThrowStatement catchThrow]
                && Dispose(catchCleanup, name) && (catchThrow.Expression is null || Name(catchThrow.Expression, catcher.VariableName));
            if (!directCatch)
            {
                if (catchBody.Statements.ToArray() is not [ExpressionStatement { Expression: AssignmentExpression
                        { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression saved, Right: var caught } }, var exit]
                    || exit is not (GotoStatement or BreakStatement)
                    || !Name(caught, catcher.VariableName)) continue;
                savedName = saved.Identifier;
                failureLabel = (exit as GotoStatement)?.Label;
                mergedCatch = exit is BreakStatement;
            }
            var before = parts.TakeWhile(s => s != guarded).ToArray();
            if (before.Any(s => s is not VariableDeclarationStatement d || d.Variables.Any(v => v.Initializer is not null))) continue;
            var tail = parts.SkipWhile(s => s != guarded).Skip(1).ToArray();
            if (earlyExit) tail = new Statement[] { new BreakStatement() }.Concat(tail).ToArray();
            var siblings = parent.Statements.ToArray();
            var index = Array.IndexOf(siblings, loop);
            var removed = new List<Statement>();
            IfElseStatement? continuation = null;
            string? mergedException = null;
            if (directCatch)
            {
                if (tail is [var internalCleanup, BreakStatement] && Dispose(internalCleanup, name)) { }
                else if (tail is [BreakStatement] && index + 1 < siblings.Length && Dispose(siblings[index + 1], name)) removed.Add(siblings[index + 1]);
                else continue;
            }
            else if (mergedCatch)
            {
                if (tail is not [var emptyCatch, BreakStatement] || !Set(emptyCatch, savedName!, null)
                    || index + 2 >= siblings.Length || !Dispose(siblings[index + 1], name)
                    || siblings[index + 2] is not IfElseStatement rethrow || rethrow.FalseStatement is not null) continue;
                mergedException = savedName;
                removed.Add(siblings[index + 1]);
                if (NullTest(rethrow.Condition, savedName!, BinaryOperatorType.InEquality)
                    && rethrow.TrueStatement is BlockStatement { Statements.Count: 1 } throwBody
                    && throwBody.Statements.Single() is ThrowStatement finalThrow && Name(finalThrow.Expression, savedName)) removed.Add(rethrow);
                else if (NullTest(rethrow.Condition, savedName!, BinaryOperatorType.Equality)
                    && rethrow.TrueStatement is BlockStatement && index + 3 < siblings.Length
                    && siblings[index + 3] is ThrowStatement failed && Name(failed.Expression, savedName))
                { continuation = rethrow; removed.Add(failed); }
                else continue;
            }
            else if (tail is [var normalCleanup, BreakStatement, LabelStatement internalLabel, var failureCleanup, IfElseStatement emptyBreak, ThrowStatement internalThrow]
                && Dispose(normalCleanup, name) && internalLabel.Label == failureLabel && Dispose(failureCleanup, name)
                && NullTest(emptyBreak.Condition, savedName!, BinaryOperatorType.Equality) && emptyBreak.FalseStatement is null
                && emptyBreak.TrueStatement is BlockStatement { Statements.Count: 1 } breakBody
                && breakBody.Statements.Single() is BreakStatement && Name(internalThrow.Expression, savedName)) { }
            else
            {
                if (index + 1 >= siblings.Length || !Dispose(siblings[index + 1], name)) continue;
                removed.Add(siblings[index + 1]);
                if (tail is [BreakStatement, LabelStatement directLabel, var directCleanup, ThrowStatement directThrow]
                    && directLabel.Label == failureLabel && Dispose(directCleanup, name) && Name(directThrow.Expression, savedName)) { }
                else if (tail is [BreakStatement, LabelStatement label, var cleanup, IfElseStatement empty, ThrowStatement thrown]
                    && label.Label == failureLabel && Dispose(cleanup, name) && NullTest(empty.Condition, savedName!, BinaryOperatorType.Equality)
                    && empty.FalseStatement is null && empty.TrueStatement is BlockStatement { Statements.Count: 1 } emptyBody
                    && emptyBody.Statements.Single() is ReturnStatement { Expression: null } && Name(thrown.Expression, savedName)) { }
                else if (tail is [ExpressionStatement { Expression: AssignmentExpression { Left: IdentifierExpression merged } }, BreakStatement,
                    LabelStatement mergeLabel, var copy, BreakStatement] && mergeLabel.Label == failureLabel
                    && Set(tail[0], merged.Identifier, null) && Set(copy, merged.Identifier, savedName)
                    && index + 2 < siblings.Length && siblings[index + 2] is IfElseStatement rethrow && rethrow.FalseStatement is null)
                {
                    mergedException = merged.Identifier;
                    if (NullTest(rethrow.Condition, merged.Identifier, BinaryOperatorType.InEquality)
                        && rethrow.TrueStatement is BlockStatement { Statements.Count: 1 } throwBody
                        && throwBody.Statements.Single() is ThrowStatement finalThrow && Name(finalThrow.Expression, merged.Identifier)) removed.Add(rethrow);
                    else if (NullTest(rethrow.Condition, merged.Identifier, BinaryOperatorType.Equality)
                        && rethrow.TrueStatement is BlockStatement && index + 3 < siblings.Length
                        && siblings[index + 3] is ThrowStatement failed && Name(failed.Expression, merged.Identifier))
                    { continuation = rethrow; removed.Add(failed); }
                    else continue;
                }
                else continue;
            }
            // 只接收元素读取以外不使用枚举器的循环体。
            if (body.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == name) != 1) continue;
            var prefix = siblings.Take(index).Reverse().SkipWhile(s => s is VariableDeclarationStatement d
                && d.Variables.All(v => v.Initializer is null or PrimitiveExpression or NullReferenceExpression or DefaultValueExpression)).ToArray();
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
            var exceptionUses = allowed.Concat(continuation?.Condition.DescendantsAndSelf.OfType<IdentifierExpression>() ?? []).ToHashSet();
            if (mergedException is not null && method.Descendants.OfType<IdentifierExpression>()
                .Any(id => id.Identifier == mergedException && !exceptionUses.Contains(id))) continue;
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == name && !allowed.Contains(id)
                && !IndependentUse(id, name, assignment, method))) continue;
            var declarations = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == name)).ToArray();
            if (declarations is not [var declaration] || declaration.Variables.Count != 1
                || declaration.Variables.Single().Initializer is not DefaultValueExpression) continue;
            var replacement = (BlockStatement)body.Clone();
            var item = current?.Variables.Single().Name ?? "item";
            if (current is not null) replacement.Statements.First().Remove();
            else
            {
                var names = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                    .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name))
                    .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
                for (var suffix = 2; names.Contains(item); suffix++) item = "item" + suffix;
                replacement.Descendants.OfType<MemberReferenceExpression>().Single(m => m.MemberName == "Current" && Name(m.Target, name))
                    .ReplaceWith(new IdentifierExpression(item));
            }
            replacement.Statements.Last().Remove();
            loop.ReplaceWith(new ForeachStatement(current?.Type.Clone() ?? new SimpleType("var"), new SingleVariableDesignation(item), get.Target.Clone(), replacement));
            foreach (var statement in removed) statement.Remove();
            if (continuation is not null)
            {
                var statements = continuation.TrueStatement;
                statements.Remove();
                continuation.ReplaceWith(statements);
            }
            assignment.Remove(); factory?.Remove();
            if (!method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == name)) declaration.Remove();
            foreach (var unused in method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Count == 1
                && d.Variables.Single().Initializer is null && !method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == d.Variables.Single().Name)).ToArray()) unused.Remove();
        }
        foreach (var (loop, original) in normalized)
            if (loop.Parent is not null) loop.ReplaceWith(original);
        RecoverAsyncLoops(rootNode);
        RecoverGuardedAsyncLoops(rootNode);
        RecoverMergedLoops(rootNode);
        RecoverNullableMergedLoops(rootNode);
        if (context?.TypeSystem is { } compilation) RecoverAny(rootNode, compilation);
        foreach (var (declaration, replacement, original) in typedReads)
            if (rootNode.Descendants.Contains(declaration)) { replacement.ReplaceWith(original); declaration.Remove(); }
    }
}
