using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    private static bool IntegerConstant(Expression? expression, ulong expected) => expression is PrimitiveExpression p && p.Value switch
    {
        int n => n >= 0 && (ulong)n == expected,
        uint n => n == expected,
        long n => n >= 0 && (ulong)n == expected,
        ulong n => n == expected,
        _ => false,
    };

    // 查找循环把 MoveNext 的结果带到循环外；耗尽为零，提前结束为一。
    private static void RecoverSearchLoops(AstNode root)
    {
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().ToArray())
        {
            if (guarded.Parent is not BlockStatement parent || guarded.Ancestors.OfType<TryCatchStatement>().Any()
                || guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || guarded.TryBlock is not { } tryBody || tryBody.Statements.LastOrDefault() is not DoWhileStatement loop
                || loop.EmbeddedStatement is not BlockStatement content
                || content.Statements.Take(5).ToArray() is not [LabelStatement head, VariableDeclarationStatement advance,
                    ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression result,
                        Right: ConditionalExpression { Condition: IdentifierExpression copied, TrueExpression: var one, FalseExpression: var zero } } },
                    IfElseStatement { Condition: UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: var tested }, FalseStatement: null,
                        TrueStatement: BlockStatement { Statements.Count: 1 } exhausted }, VariableDeclarationStatement current]
                || advance.Variables.ToArray() is not [var flag] || flag.Name != copied.Identifier || !Name(tested, flag.Name)
                || flag.Initializer is not InvocationExpression { Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }
                || !IntegerConstant(one, 1) || !IntegerConstant(zero, 0) || exhausted.Statements.Single() is not BreakStatement
                || current.Variables.ToArray() is not [var element]
                || element.Initializer is not MemberReferenceExpression { MemberName: "Current", Target: var receiver } read
                || !Name(receiver, enumerator.Identifier) || CurrentByReference(read)
                || catcher.Body?.Statements.ToArray() is not [var disposed, ThrowStatement thrown]
                || !Dispose(disposed, enumerator.Identifier) || thrown.Expression is not null && !Name(thrown.Expression, catcher.VariableName)) continue;
            var before = tryBody.Statements.TakeWhile(s => s != loop).ToArray();
            var condition = loop.Condition is UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: var operand } ? operand : loop.Condition;
            if (condition is not IdentifierExpression conditionName || before.Any(s => s is not VariableDeclarationStatement d || d.Variables.Any(v => v.Initializer is not null))
                || !before.OfType<VariableDeclarationStatement>().SelectMany(d => d.Variables).Any(v => v.Name == conditionName.Identifier)
                || content.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == enumerator.Identifier) != 2
                || content.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == flag.Name) != 2
                || content.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == result.Identifier) != 1) continue;
            var statements = parent.Statements.ToArray();
            var index = Array.IndexOf(statements, guarded);
            if (index + 1 >= statements.Length || !Dispose(statements[index + 1], enumerator.Identifier)) continue;
            var initialization = statements.Take(index).Reverse().SkipWhile(s => s is VariableDeclarationStatement d && d.Variables.All(v => v.Initializer is null)).FirstOrDefault();
            if (initialization is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var target,
                    Right: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get } factory } }
                || !Name(target, enumerator.Identifier)
                || !Enumerator(factory).Disposable
                || guarded.GetParent<MethodDeclaration>() is not { } method) continue;
            var enumDeclarations = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == enumerator.Identifier)).ToArray();
            var resultDeclarations = method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == result.Identifier)).ToArray();
            if (enumDeclarations is not [var enumDeclaration] || enumDeclaration.Variables.ToArray() is not [{ Initializer: DefaultValueExpression }]
                || resultDeclarations is not [var resultDeclaration] || resultDeclaration.Variables.ToArray() is not [{ Initializer: null } resultVariable]
                || resultDeclaration.Parent != parent) continue;
            var allowed = guarded.Descendants.Concat(initialization.Descendants).Concat(statements[index + 1].Descendants).ToHashSet();
            var afterwards = statements.Skip(index + 2).SelectMany(s => s.Descendants).ToHashSet();
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == enumerator.Identifier && !allowed.Contains(id)
                || id.Identifier == result.Identifier && id != result && !afterwards.Contains(id))) continue;
            var labels = content.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            if (content.Descendants.OfType<ReturnStatement>().Any()
                || content.Descendants.OfType<GotoStatement>().Any(j => j.Label is null || !labels.Contains(j.Label))
                || method.Descendants.OfType<GotoStatement>().Any(j => j.Label is not null && labels.Contains(j.Label) && !content.Descendants.Contains(j))) continue;
            static AstNode? LoopOf(AstNode node) => node.Ancestors.FirstOrDefault(n => n is WhileStatement or DoWhileStatement or ForStatement or ForeachStatement);
            if (content.Descendants.OfType<ContinueStatement>().Any(c => LoopOf(c) == loop
                && c.Ancestors.TakeWhile(n => n != loop).OfType<SwitchStatement>().Any())) continue;
            if (content.Descendants.OfType<BreakStatement>().Any(b => b != exhausted.Statements.Single()
                && b.Ancestors.FirstOrDefault(n => n is WhileStatement or DoWhileStatement or ForStatement or ForeachStatement or SwitchStatement) == loop)) continue;
            bool UsesElement(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(id => id.Identifier == element.Name);
            if (content.Descendants.OfType<AssignmentExpression>().Any(a => UsesElement(a.Left))
                || content.Descendants.OfType<DirectionExpression>().Any(d => UsesElement(d.Expression))
                || content.Descendants.OfType<UnaryOperatorExpression>().Any(u => u.Operator is UnaryOperatorType.Increment or UnaryOperatorType.Decrement
                    or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf && UsesElement(u.Expression))) continue;
            var occupied = method.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            string Label(string seed) { var name = seed; for (var n = 2; occupied.Contains(name); n++) name = seed + n; occupied.Add(name); return name; }
            var next = Label("nextItem");
            var stopCondition = loop.Condition is UnaryOperatorExpression { Operator: UnaryOperatorType.Not, Expression: var inverted }
                ? inverted.Clone() : new UnaryOperatorExpression(UnaryOperatorType.Not, loop.Condition!.Clone());
            var stop = new IfElseStatement(stopCondition, new BlockStatement
                { new ExpressionStatement(new AssignmentExpression(new IdentifierExpression(result.Identifier), one!.Clone())), new BreakStatement() });
            var body = new BlockStatement();
            foreach (var statement in before) body.Statements.Add(statement.Clone());
            foreach (var statement in content.Statements.Skip(5))
            {
                var copy = statement.Clone();
                var originalContinues = statement.DescendantsAndSelf.OfType<ContinueStatement>().ToArray();
                var copiedContinues = copy.DescendantsAndSelf.OfType<ContinueStatement>().ToArray();
                for (var n = 0; n < originalContinues.Length; n++)
                    if (LoopOf(originalContinues[n]) == loop)
                    {
                        if (originalContinues[n] == statement) body.Statements.Add(stop.Clone());
                        else if (copiedContinues[n].Parent is BlockStatement local) local.Statements.InsertBefore(copiedContinues[n], stop.Clone());
                        else copiedContinues[n].ReplaceWith(new BlockStatement { stop.Clone(), new ContinueStatement() });
                    }
                var originalJumps = statement.DescendantsAndSelf.OfType<GotoStatement>().Where(j => j.Label == head.Label).ToArray();
                var copiedJumps = copy.DescendantsAndSelf.OfType<GotoStatement>().Where(j => j.Label == head.Label).ToArray();
                for (var n = 0; n < originalJumps.Length; n++)
                    if (LoopOf(originalJumps[n]) != loop) copiedJumps[n].Label = next;
                    else if (originalJumps[n] == statement) copy = new ContinueStatement();
                    else copiedJumps[n].ReplaceWith(new ContinueStatement());
                body.Statements.Add(copy);
            }
            if (body.Statements.LastOrDefault() is not (ContinueStatement or GotoStatement or ThrowStatement)) body.Statements.Add(stop);
            if (body.Descendants.OfType<GotoStatement>().Any(j => j.Label == next))
            { body.Statements.Add(new LabelStatement(next)); body.Statements.Add(new EmptyStatement()); }
            resultVariable.Initializer = zero!.Clone();
            guarded.ReplaceWith(new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(element.Name), get.Target.Clone(), body));
            statements[index + 1].Remove(); initialization.Remove(); enumDeclaration.Remove();
        }
    }
}
