using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    // 耗尽检查在循环开头时，建立相同的正向分支视图；未恢复的循环原样还原。
    private static List<(WhileStatement Original, WhileStatement Replacement)> NormalizeExhaustedResults(AstNode root)
    {
        var changed = new List<(WhileStatement, WhileStatement)>();
        foreach (var loop in root.Descendants.OfType<WhileStatement>().ToArray())
        {
            if (loop.Condition is not PrimitiveExpression { Value: true } || loop.EmbeddedStatement is not BlockStatement body
                || body.Statements.FirstOrDefault() is not IfElseStatement { FalseStatement: null,
                    Condition: UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: InvocationExpression { Arguments.Count: 0,
                        Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression } } advance },
                    TrueStatement: BlockStatement exhausted }
                || exhausted.Statements.LastOrDefault() is not BreakStatement) continue;
            var positive = new BlockStatement();
            foreach (var statement in body.Statements.Skip(1)) positive.Statements.Add(statement.Clone());
            if (positive.Statements.LastOrDefault() is not (BreakStatement or ContinueStatement)) positive.Statements.Add(new ContinueStatement());
            var content = new BlockStatement { new IfElseStatement(advance.Clone(), positive) };
            foreach (var statement in exhausted.Statements) content.Statements.Add(statement.Clone());
            var replacement = new WhileStatement(loop.Condition.Clone(), content);
            loop.ReplaceWith(replacement);
            changed.Add((loop, replacement));
        }
        return changed;
    }

    // 结果常量可前置；局部回退值在耗尽后复制，命中路径直接跳过该复制。
    private static void RecoverResultLoops(AstNode root)
    {
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().ToArray())
        {
            if (guarded.Parent is not BlockStatement parent
                || guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || guarded.TryBlock?.Statements.LastOrDefault() is not WhileStatement { Condition: PrimitiveExpression { Value: true }, EmbeddedStatement: BlockStatement content } loop
                || content.Statements.FirstOrDefault() is not IfElseStatement { FalseStatement: null, Condition: InvocationExpression { Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }, TrueStatement: BlockStatement positive }
                || positive.Statements.FirstOrDefault() is not VariableDeclarationStatement current || current.Variables.ToArray() is not [var element]
                || element.Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var receiver } read || !Name(receiver, enumerator.Identifier)
                || CurrentByReference(read)
                || positive.Statements.LastOrDefault() is not (ContinueStatement or BreakStatement)
                || guarded.GetParent<MethodDeclaration>() is not { } method) continue;
            var prefix = guarded.TryBlock.Statements.TakeWhile(s => s != loop).ToArray();
            if (prefix.Length != 0 && (prefix is not [IfElseStatement guard]
                || !NullTest(guard.Condition, enumerator.Identifier, BinaryOperatorType.Equality) || guard.FalseStatement is not null
                || guard.TrueStatement is not BlockStatement { Statements.Count: 1 } missing
                || missing.Statements.Single() is not ThrowStatement { Expression: ObjectCreateExpression { Arguments.Count: 0 } error }
                || error.Type?.ToString() is not ("NullReferenceException" or "System.NullReferenceException"))) continue;
            var tail = content.Statements.Skip(1).ToArray();
            var defaults = tail.TakeWhile(s => s is not BreakStatement).ToArray();
            if (defaults.Length == 0 || defaults.Any(s => s is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                Left: IdentifierExpression, Right: PrimitiveExpression or NullReferenceExpression or IdentifierExpression } })) continue;
            var writes = defaults.Cast<ExpressionStatement>().Select(s => (AssignmentExpression)s.Expression).ToArray();
            var fallback = writes.Any(a => a.Right is IdentifierExpression);
            if (fallback ? writes.Length != 1 : guarded.Ancestors.OfType<TryCatchStatement>().Any()) continue;
            var names = writes.Select(a => ((IdentifierExpression)a.Left).Identifier).ToHashSet();
            if (names.Count != writes.Length) continue;
            var suffix = tail.Skip(defaults.Length).Where(s => s is not ContinueStatement).ToArray();
            string? exit = null;
            if (suffix is [BreakStatement, LabelStatement label, BreakStatement]) exit = label.Label;
            else if (suffix is not [BreakStatement]) continue;
            if (fallback && exit is not null) continue;
            var statements = parent.Statements.ToArray(); var index = Array.IndexOf(statements, guarded);
            if (index + 1 >= statements.Length) continue;
            var conditionalInterface = InterfaceCleanup(catcher, statements[index + 1], enumerator.Identifier, method);
            if (!conditionalInterface && (!ConditionalCleanup(catcher, enumerator.Identifier)
                || !Dispose(statements[index + 1], enumerator.Identifier))) continue;
            var initialization = statements.Take(index).Reverse().SkipWhile(s => s is VariableDeclarationStatement d
                && (d.Variables.All(v => v.Initializer is null) || fallback && PureLocals(s))).FirstOrDefault();
            var initialized = initialization switch
            {
                VariableDeclarationStatement d when d.Variables.ToArray() is [var v] && v.Name == enumerator.Identifier => v.Initializer,
                ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var target, Right: var value } }
                    when Name(target, enumerator.Identifier) => value,
                _ => null,
            };
            if (initialized is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get } factory
                || (conditionalInterface ? factory.Annotation<ResolveResult>()?.Type.FullName != "System.Collections.IEnumerator"
                    : !Enumerator(factory).Disposable)) continue;
            if (fallback && (!LocalResultCopy(defaults[0], parent, guarded, method)
                || !StableCopies(method, statements.SkipWhile(s => s != initialization).Skip(1).TakeWhile(s => s != guarded), factory))) continue;
            var declarations = statements.Take(index).OfType<VariableDeclarationStatement>()
                .Where(d => d.Variables.Any(v => names.Contains(v.Name))).ToArray();
            if (declarations.Length != names.Count || declarations.Any(d => d.Variables.ToArray() is not [{ Initializer: null }])) continue;
            var enumDeclarations = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == enumerator.Identifier)).ToArray();
            if (enumDeclarations is not [var enumDeclaration] || enumDeclaration != initialization
                && enumDeclaration.Variables.ToArray() is not [{ Initializer: DefaultValueExpression }]) continue;
            var allowed = guarded.Descendants.Concat(initialization!.Descendants).Concat(statements[index + 1].Descendants).ToHashSet();
            if (positive.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == enumerator.Identifier) != 1
                || method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == enumerator.Identifier && !allowed.Contains(id))
                || positive.Descendants.OfType<IdentifierExpression>().Any(id => names.Contains(id.Identifier)
                    && (id.Parent is not AssignmentExpression { Operator: AssignmentOperatorType.Assign } assignment || assignment.Left != id))) continue;
            var before = statements.Take(index).SelectMany(s => s.Descendants).ToHashSet();
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => names.Contains(id.Identifier) && before.Contains(id))) continue;
            var labels = positive.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            if (exit is not null) labels.Add(exit);
            if (positive.Descendants.OfType<ReturnStatement>().Any()
                || positive.Descendants.OfType<GotoStatement>().Any(j => j.Label is null || !labels.Contains(j.Label))
                || method.Descendants.OfType<GotoStatement>().Any(j => j.Label is not null && labels.Contains(j.Label) && !positive.Descendants.Contains(j))) continue;
            bool UsesElement(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => id.Identifier == element.Name);
            if (positive.Descendants.OfType<AssignmentExpression>().Any(a => UsesElement(a.Left))
                || positive.Descendants.OfType<DirectionExpression>().Any(d => UsesElement(d.Expression))
                || positive.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                    or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && UsesElement(u.Expression))) continue;
            var body = (BlockStatement)positive.Clone(); body.Statements.First().Remove();
            if (body.Statements.Last() is ContinueStatement) body.Statements.Last().Remove();
            string? completed = null;
            if (fallback)
            {
                var used = method.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
                completed = "enumerationDone";
                for (var n = 2; used.Contains(completed); n++) completed = "enumerationDone" + n;
                foreach (var stopped in body.Descendants.OfType<BreakStatement>().Where(b => !b.Ancestors.TakeWhile(n => n != body)
                    .Any(n => n is WhileStatement or DoWhileStatement or ForStatement or ForeachStatement or SwitchStatement
                        or LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement)).ToArray())
                    stopped.ReplaceWith(new GotoStatement(completed));
            }
            var rewrite = new ForeachRewrite(guarded, new(current.Type, element.Name, get.Target, body));
            if (!fallback) foreach (var declaration in declarations)
            {
                var variable = declaration.Variables.Single();
                rewrite.Initializers.Add((variable, writes.Single(a => Name(a.Left, variable.Name)).Right));
            }
            var replacement = rewrite.Loop;
            if (completed is not null)
            {
                var exhausted = defaults[0].Clone();
                var done = new LabelStatement(completed);
                rewrite.Suffix.AddRange([exhausted, done, new EmptyStatement()]);
            }
            if (exit is not null)
            {
                var exitLabel = new LabelStatement(exit);
                rewrite.Suffix.InsertRange(0, [exitLabel, new EmptyStatement()]);
            }
            rewrite.Removed.AddRange([statements[index + 1], initialization, enumDeclaration]);
            rewrite.Commit();
            if (exit is not null && parent == method.Body) FoldResultReturns(method, replacement, declarations, exit);
        }
    }

    private static void FoldResultReturns(MethodDeclaration method, ForeachStatement loop, VariableDeclarationStatement[] declarations, string exit)
    {
        var tail = method.Body!.Statements.SkipWhile(s => s != loop).Skip(1).Where(s => s is not EmptyStatement).ToArray();
        if (tail is not [LabelStatement label, ReturnStatement returned] || label.Label != exit || returned.Expression is null) return;
        var initial = declarations.ToDictionary(d => d.Variables.Single().Name, d => d.Variables.Single().Initializer!);
        static object? Constant(Expression? expression, IReadOnlyDictionary<string, Expression> values)
        {
            if (expression is IdentifierExpression id) return values.TryGetValue(id.Identifier, out var v) && v is PrimitiveExpression ? Constant(v, values) : null;
            if (expression is PrimitiveExpression p) return p.Value switch
            {
                bool flag => flag, byte n => (ulong)n, ushort n => (ulong)n, uint n => (ulong)n, ulong n => n,
                sbyte n when n >= 0 => (ulong)n, short n when n >= 0 => (ulong)n, int n when n >= 0 => (ulong)n, long n when n >= 0 => (ulong)n,
                _ => null,
            };
            if (expression is ParenthesizedExpression parentheses) return Constant(parentheses.Expression, values);
            if (expression is CastExpression { Type: PrimitiveType type } cast && Constant(cast.Expression, values) is ulong number)
            {
                ulong maximum = type.Keyword switch { "byte" => byte.MaxValue, "sbyte" => (ulong)sbyte.MaxValue, "short" => (ulong)short.MaxValue,
                    "ushort" => ushort.MaxValue, "int" => int.MaxValue, "uint" => uint.MaxValue, "long" => long.MaxValue, "ulong" => ulong.MaxValue, _ => 0UL };
                return maximum > 0 && number <= maximum ? number : null;
            }
            if (expression is ConditionalExpression choice && Constant(choice.Condition, values) is bool condition)
                return Constant(condition ? choice.TrueExpression : choice.FalseExpression, values);
            if (expression is UnaryOperatorExpression { Operator: UnaryOperatorType.Not } negated && Constant(negated.Expression, values) is bool boolean) return !boolean;
            if (expression is not BinaryOperatorExpression binary) return null;
            var left = Constant(binary.Left, values); var right = Constant(binary.Right, values);
            if (left is ulong a && right is ulong b) return binary.Operator switch
            {
                BinaryOperatorType.BitwiseAnd => a & b, BinaryOperatorType.BitwiseOr => a | b,
                BinaryOperatorType.Equality => a == b, BinaryOperatorType.InEquality => a != b,
                _ => null,
            };
            return null;
        }
        if (Constant(returned.Expression, initial) is not bool exhausted) return;
        var jumps = method.Descendants.OfType<GotoStatement>().Where(j => j.Label == exit).ToArray();
        if (jumps.Length == 0 || jumps.Any(j => !loop.Descendants.Contains(j))) return;
        var paths = new List<(GotoStatement Jump, Statement[] Writes, bool Result)>();
        foreach (var jump in jumps)
        {
            var preceding = jump.Parent switch { BlockStatement block => block.Statements, SwitchSection section => section.Statements, _ => null };
            if (preceding is null) return;
            var writes = preceding.TakeWhile(s => s != jump).Reverse().TakeWhile(s => s is ExpressionStatement
                { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression id, Right: PrimitiveExpression } }
                && initial.ContainsKey(id.Identifier)).Reverse().ToArray();
            var assignments = writes.Cast<ExpressionStatement>().Select(s => (AssignmentExpression)s.Expression).ToArray();
            if (assignments.Length != initial.Count || assignments.Select(a => ((IdentifierExpression)a.Left).Identifier).Distinct().Count() != initial.Count) return;
            var state = assignments.ToDictionary(a => ((IdentifierExpression)a.Left).Identifier, a => a.Right);
            if (Constant(returned.Expression, state) is not bool result) return;
            paths.Add((jump, writes, result));
        }
        var allowed = returned.Descendants.Concat(paths.SelectMany(p => p.Writes).SelectMany(s => s.Descendants)).ToHashSet();
        if (method.Descendants.OfType<IdentifierExpression>().Any(id => initial.ContainsKey(id.Identifier) && !allowed.Contains(id))) return;
        foreach (var path in paths)
        {
            path.Jump.ReplaceWith(new ReturnStatement(new PrimitiveExpression(path.Result)));
            foreach (var write in path.Writes) write.Remove();
        }
        foreach (var declaration in declarations) declaration.Remove();
        foreach (var statement in method.Body.Statements.SkipWhile(s => s != loop).Skip(1).ToArray()) statement.Remove();
        method.Body.Statements.Add(new ReturnStatement(new PrimitiveExpression(exhausted)));
    }
}
