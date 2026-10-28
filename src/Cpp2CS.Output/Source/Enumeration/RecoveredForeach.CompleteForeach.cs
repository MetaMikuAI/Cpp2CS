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
        string exceptional;
        if (catcher.Body?.Statements.ToArray() is [IfElseStatement { FalseStatement: null,
            Condition: UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: var rejected },
            TrueStatement: BlockStatement { Statements.Count: 1 } absent }, var exceptionalDispose, var finalThrow]
            && DisposablePattern(rejected, name, out var pattern) && Rethrow(absent.Statements.Single())
            && Dispose(exceptionalDispose, pattern) && Rethrow(finalThrow)) exceptional = pattern;
        else if (catcher.Body?.Statements.ToArray() is [VariableDeclarationStatement declaration,
            IfElseStatement { FalseStatement: null, TrueStatement: BlockStatement { Statements.Count: 1 } missing } check, var cleanup, var thrown]
            && declaration.Variables.ToArray() is [var variable]
            && variable.Initializer is AsExpression { Expression: var receiver, Type: var type }
            && Name(receiver, name) && type.Annotation<ResolveResult>()?.Type.FullName == "System.IDisposable"
            && NullTest(check.Condition, variable.Name, BinaryOperatorType.Equality) && Rethrow(missing.Statements.Single())
            && Dispose(cleanup, variable.Name) && Rethrow(thrown)) exceptional = variable.Name;
        else return false;
        if (normal is not IfElseStatement { FalseStatement: null, Condition: var accepted,
                TrueStatement: BlockStatement { Statements.Count: 1 } present }
            || !DisposablePattern(accepted, name, out var ordinary) || !Dispose(present.Statements.Single(), ordinary)) return false;
        var allowed = catcher.Descendants.Concat(normal.Descendants).ToHashSet();
        return !method.Descendants.OfType<IdentifierExpression>().Any(id => (id.Identifier == exceptional || id.Identifier == ordinary) && !allowed.Contains(id));
    }

    // 结果局部只活在清理所在块中；释放抛错离开该作用域时，延后复制不能被观察。
    private static bool LocalResultCopy(Statement statement, BlockStatement parent, Statement guarded, AstNode method)
    {
        if (statement is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                Left: IdentifierExpression left, Right: IdentifierExpression right } }
            || left.GetILVariable() is not { Type.Kind: not TypeKind.ByReference, AddressInstructions.Count: 0, CaptureScope: null } target
            || right.GetILVariable() is not { Type.Kind: not TypeKind.ByReference, AddressInstructions.Count: 0, CaptureScope: null } source
            || !target.Type.Equals(source.Type)
            || !parent.Statements.TakeWhile(s => s != guarded).OfType<VariableDeclarationStatement>()
                .Any(d => d.Variables.Any(v => v.Name == left.Identifier))) return false;
        return !method.Descendants.OfType<IdentifierExpression>().Any(id => (id.GetILVariable() == target || id.GetILVariable() == source)
            && id.Ancestors.TakeWhile(n => n != method).Any(n => n is LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement));
    }

    // 完整 try/while 加正常清理；允许可写元素局部和工厂附近的纯局部初始化。
    private static void RecoverCompleteLoops(AstNode root)
    {
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().Reverse().ToArray())
        {
            if (guarded.Parent is not BlockStatement parent || guarded.FinallyBlock is not null
                || guarded.CatchClauses.ToArray() is not [var catcher] || catcher.Condition is not null
                || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || guarded.TryBlock?.Statements.OfType<WhileStatement>().LastOrDefault() is not WhileStatement
                    { Condition: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } },
                        EmbeddedStatement: BlockStatement body } originalLoop
                || body.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.ToArray() is not [var element]
                || CurrentRead(element.Initializer) is not { Target: var receiver } read || !Name(receiver, enumerator.Identifier)
                || CurrentByReference(read)) continue;
            var inside = guarded.TryBlock.Statements.TakeWhile(s => s != originalLoop).ToArray();
            var trailing = guarded.TryBlock.Statements.SkipWhile(s => s != originalLoop).Skip(1).ToArray();
            IfElseStatement? guard = null;
            if (inside.FirstOrDefault() is IfElseStatement test && NullTest(test.Condition, enumerator.Identifier, BinaryOperatorType.Equality)
                && test.FalseStatement is null && test.TrueStatement is BlockStatement { Statements.Count: 1 } absent
                && absent.Statements.Single() is ThrowStatement { Expression: ObjectCreateExpression { Arguments.Count: 0 } error }
                && error.Type?.ToString() is "NullReferenceException" or "System.NullReferenceException") { guard = test; inside = inside.Skip(1).ToArray(); }
            if (inside.Any(s => !PureLocals(s))) continue;
            var siblings = parent.Statements.ToArray(); var index = Array.IndexOf(siblings, guarded);
            if (index + 1 >= siblings.Length
                || guarded.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is not { } method) continue;
            if (trailing.Any(s => !LocalResultCopy(s, parent, guarded, method))) continue;
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
            VariableDeclarationStatement? factoryCopy = null;
            var between = Array.Empty<Statement>();
            if (initialized is IdentifierExpression temporary)
            {
                var beforeFactory = siblings.TakeWhile(s => s != factory).ToArray();
                between = beforeFactory.Reverse().TakeWhile(PureLocals).Reverse().ToArray();
                if (beforeFactory.Take(beforeFactory.Length - between.Length).LastOrDefault() is not VariableDeclarationStatement copied
                    || copied.Variables.ToArray() is not [var variable] || variable.Name != temporary.Identifier
                    || method.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == temporary.Identifier) != 1) continue;
                factoryCopy = copied;
                initialized = variable.Initializer;
            }
            if (initialized is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get } invocation
                || !StableCopies(method, prefix.Concat(inside).Concat(between), invocation)) continue;
            var iteratorType = invocation.Annotation<ResolveResult>()?.Type;
            if (conditionalInterface ? iteratorType?.FullName != "System.Collections.IEnumerator"
                : !Enumerator(iteratorType).Disposable) continue;
            if (!conditionalInterface && iteratorType!.IsReferenceType == true && !NullableDispose(siblings[index + 1], enumerator.Identifier)
                && catcher.Body!.Statements.FirstOrDefault() is not IfElseStatement) continue;
            var exitDisposals = ExitDisposals(body, method, parent, guarded, enumerator.Identifier);
            if (exitDisposals is null) continue;
            var removed = new List<Statement> { factory!, siblings[index + 1] };
            if (factoryCopy is not null) removed.Add(factoryCopy);
            removed.AddRange(exitDisposals);
            if (index + 2 < siblings.Length && siblings[index + 2] is ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                Left: var reset, Right: DefaultValueExpression } } && Name(reset, enumerator.Identifier)) removed.Add(siblings[index + 2]);
            var allowed = removed.SelectMany(s => s.Descendants).Concat(catcher.Descendants).Concat(guard?.Descendants ?? [])
                .Concat(originalLoop.Condition!.DescendantsAndSelf).Concat(read.Descendants).ToHashSet();
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == enumerator.Identifier && !allowed.Contains(id)
                && !IndependentUse(id, enumerator.Identifier, factory!, method))) continue;
            var declarations = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == enumerator.Identifier)).ToArray();
            if (declarations is not [var declaration] || declaration != factory && declaration.Variables.ToArray() is not [{ Initializer: DefaultValueExpression }]) continue;
            var labels = body.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            if (body.Descendants.OfType<ReturnStatement>().Any(returned => !returned.Ancestors.TakeWhile(n => n != body)
                    .Any(n => n is LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement))
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
            var rewrite = new ForeachRewrite(guarded, new(current.Type, item, get.Target, content));
            rewrite.Prefix.AddRange(inside.Select(s => s.Clone()));
            rewrite.Suffix.AddRange(trailing.Select(s => s.Clone()));
            rewrite.Removed.AddRange(removed);
            rewrite.Commit();
            if (declaration != factory && !method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == enumerator.Identifier)) declaration.Remove();
        }
    }
}
