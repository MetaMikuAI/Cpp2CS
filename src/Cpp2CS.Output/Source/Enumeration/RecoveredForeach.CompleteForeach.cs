using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    private static bool PureLocals(Statement statement) => statement is VariableDeclarationStatement declaration
        && declaration.Variables.All(v => v.Initializer is null or IdentifierExpression or PrimitiveExpression or NullReferenceExpression or DefaultValueExpression);

    private static bool StableCopies(AstNode method, IEnumerable<Statement> prefix, Expression factory)
    {
        var names = prefix.SelectMany(s => s.Descendants.OfType<IdentifierExpression>()).Select(id => id.Identifier).ToHashSet();
        var locals = method.Descendants.OfType<VariableInitializer>().Select(v => v.Name)
            .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
        bool Reads(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => names.Contains(id.Identifier));
        return names.All(locals.Contains)
            && !method.Descendants.Where(n => n is DirectionExpression or LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement).Any(Reads)
            && !factory.Descendants.OfType<AssignmentExpression>().Any(a => Reads(a.Left))
            && !factory.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && Reads(u.Expression));
    }

    private static bool ConditionalCleanup(CatchClause catcher, string name)
    {
        bool Rethrow(Statement s) => s is ThrowStatement t && (t.Expression is null || Name(t.Expression, catcher.VariableName));
        if (catcher.Body?.Statements.ToArray() is [var dispose, var thrown] && (Dispose(dispose, name) || NullableDispose(dispose, name)) && Rethrow(thrown)) return true;
        if (catcher.Body?.Statements.ToArray() is [IfElseStatement conditional, var final]
            && NullTest(conditional.Condition, name, BinaryOperatorType.InEquality) && conditional.FalseStatement is null
            && conditional.TrueStatement is BlockStatement positive && positive.Statements.ToArray() is [var cleanupCall, var caughtThrow]
            && Dispose(cleanupCall, name) && Rethrow(caughtThrow) && Rethrow(final)) return true;
        if (catcher.Body?.Statements.ToArray() is not [IfElseStatement test, var cleanup, var finalThrow]
            || !NullTest(test.Condition, name, BinaryOperatorType.Equality) || test.FalseStatement is not null
            || test.TrueStatement is not BlockStatement { Statements.Count: 1 } body || !Rethrow(body.Statements.Single())) return false;
        return Dispose(cleanup, name) && Rethrow(finalThrow);
    }

    private static bool DisposablePattern(Expression? expression, string name, out string variable)
    {
        while (expression is ParenthesizedExpression parentheses) expression = parentheses.Expression;
        variable = "";
        if (expression is not BinaryOperatorExpression { Operator: BinaryOperatorType.IsPattern, Left: var value,
            Right: DeclarationExpression { Designation: SingleVariableDesignation designation } pattern }
            || !Name(value, name) || pattern.Type?.Annotation<ResolveResult>()?.Type.FullName != "System.IDisposable") return false;
        variable = designation.Identifier;
        return true;
    }

    private static bool InterfaceCleanup(CatchClause catcher, Statement normal, string name, AstNode method)
    {
        bool Rethrow(Statement s) => s is ThrowStatement t && (t.Expression is null || Name(t.Expression, catcher.VariableName));
        if (catcher.Body?.Statements.ToArray() is not [IfElseStatement { FalseStatement: null,
            Condition: UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: var rejected },
            TrueStatement: BlockStatement { Statements.Count: 1 } absent }, var exceptionalDispose, var finalThrow]
            || !DisposablePattern(rejected, name, out var exceptional) || !Rethrow(absent.Statements.Single())
            || !Dispose(exceptionalDispose, exceptional) || !Rethrow(finalThrow)
            || normal is not IfElseStatement { FalseStatement: null, Condition: var accepted,
                TrueStatement: BlockStatement { Statements.Count: 1 } present }
            || !DisposablePattern(accepted, name, out var ordinary) || !Dispose(present.Statements.Single(), ordinary)) return false;
        var allowed = catcher.Descendants.Concat(normal.Descendants).ToHashSet();
        return !method.Descendants.OfType<IdentifierExpression>().Any(id => (id.Identifier == exceptional || id.Identifier == ordinary) && !allowed.Contains(id));
    }

    // 完整 try/while 加正常清理；允许可写元素局部和工厂附近的纯局部初始化。
    private static void RecoverCompleteLoops(AstNode root)
    {
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().Reverse().ToArray())
        {
            if (guarded.Parent is not BlockStatement parent || guarded.FinallyBlock is not null
                || guarded.CatchClauses.ToArray() is not [var catcher] || catcher.Condition is not null
                || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || guarded.TryBlock?.Statements.LastOrDefault() is not WhileStatement
                    { Condition: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } },
                        EmbeddedStatement: BlockStatement body }
                || body.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.ToArray() is not [var element]
                || CurrentRead(element.Initializer) is not { Target: var receiver } read || !Name(receiver, enumerator.Identifier)
                || CurrentByReference(read)) continue;
            var inside = guarded.TryBlock.Statements.Take(guarded.TryBlock.Statements.Count - 1).ToArray();
            IfElseStatement? guard = null;
            if (inside.FirstOrDefault() is IfElseStatement test && NullTest(test.Condition, enumerator.Identifier, BinaryOperatorType.Equality)
                && test.FalseStatement is null && test.TrueStatement is BlockStatement { Statements.Count: 1 } absent
                && absent.Statements.Single() is ThrowStatement { Expression: ObjectCreateExpression { Arguments.Count: 0 } error }
                && error.Type?.ToString() is "NullReferenceException" or "System.NullReferenceException") { guard = test; inside = inside.Skip(1).ToArray(); }
            if (inside.Any(s => !PureLocals(s))) continue;
            var siblings = parent.Statements.ToArray(); var index = Array.IndexOf(siblings, guarded);
            if (index + 1 >= siblings.Length
                || guarded.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is not { } method) continue;
            var conditionalInterface = InterfaceCleanup(catcher, siblings[index + 1], enumerator.Identifier, method);
            if (!conditionalInterface && (!ConditionalCleanup(catcher, enumerator.Identifier)
                || !Dispose(siblings[index + 1], enumerator.Identifier) && !NullableDispose(siblings[index + 1], enumerator.Identifier))) continue;
            var prefix = siblings.Take(index).Reverse().TakeWhile(PureLocals).Reverse().ToArray();
            var factory = siblings.Take(index - prefix.Length).LastOrDefault();
            var initialized = factory switch
            {
                VariableDeclarationStatement d when d.Variables.ToArray() is [var v] && v.Name == enumerator.Identifier => v.Initializer,
                ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var target, Right: var value } }
                    when Name(target, enumerator.Identifier) => value,
                _ => null,
            };
            if (initialized is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get } invocation
                || !StableCopies(method, prefix.Concat(inside), invocation)) continue;
            var iteratorType = invocation.Annotation<ResolveResult>()?.Type;
            if (conditionalInterface ? iteratorType?.FullName != "System.Collections.IEnumerator"
                : !Enumerator(iteratorType).Disposable) continue;
            if (!conditionalInterface && iteratorType!.IsReferenceType == true && !NullableDispose(siblings[index + 1], enumerator.Identifier)
                && catcher.Body!.Statements.FirstOrDefault() is not IfElseStatement) continue;
            var removed = new List<Statement> { factory!, siblings[index + 1] };
            if (index + 2 < siblings.Length && siblings[index + 2] is ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                Left: var reset, Right: DefaultValueExpression } } && Name(reset, enumerator.Identifier)) removed.Add(siblings[index + 2]);
            var allowed = removed.SelectMany(s => s.Descendants).Concat(catcher.Descendants).Concat(guard?.Descendants ?? [])
                .Concat(((WhileStatement)guarded.TryBlock.Statements.Last()).Condition!.DescendantsAndSelf).Concat(read.Descendants).ToHashSet();
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == enumerator.Identifier && !allowed.Contains(id))) continue;
            var declarations = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == enumerator.Identifier)).ToArray();
            if (declarations is not [var declaration] || declaration != factory && declaration.Variables.ToArray() is not [{ Initializer: DefaultValueExpression }]) continue;
            var labels = body.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            if (body.Descendants.OfType<ReturnStatement>().Any() || body.Descendants.OfType<GotoStatement>().Any(j => j.Label is null || !labels.Contains(j.Label))
                || method.Descendants.OfType<GotoStatement>().Any(j => j.Label is not null && labels.Contains(j.Label) && !body.Descendants.Contains(j))) continue;
            var content = (BlockStatement)body.Clone(); var item = element.Name;
            bool UsesElement(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => id.Identifier == element.Name);
            var reference = read.Annotation<ResolveResult>()?.Type.IsReferenceType == true;
            bool NeedsCopy(Expression expression) => UsesElement(expression) && (!reference || Name(expression, element.Name));
            var writable = body.Descendants.OfType<AssignmentExpression>().Any(a => NeedsCopy(a.Left))
                || body.Descendants.OfType<DirectionExpression>().Any(d => NeedsCopy(d.Expression))
                || body.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                    or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && NeedsCopy(u.Expression));
            if (writable)
            {
                var names = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                    .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name)).Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
                item = "item"; for (var suffix = 2; names.Contains(item); suffix++) item = "item" + suffix;
                ((VariableDeclarationStatement)content.Statements.First()).Variables.Single().Initializer = new IdentifierExpression(item);
            }
            else content.Statements.First().Remove();
            var loop = new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(item), get.Target.Clone(), content);
            if (inside.Length == 0) guarded.ReplaceWith(loop);
            else { var replacement = new BlockStatement(); foreach (var s in inside) replacement.Statements.Add(s.Clone()); replacement.Statements.Add(loop); guarded.ReplaceWith(replacement); }
            foreach (var statement in removed) statement.Remove();
            if (declaration != factory) declaration.Remove();
        }
    }
}
