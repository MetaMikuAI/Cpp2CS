using ICSharpCode.Decompiler.CSharp.Syntax;

namespace Cpp2CS.Extensions.Decompile;

internal sealed partial class RecoveredForeach
{
    // 将保存 MoveNext 结果的双出口查找交给统一的结果循环检查；未通过时还原。
    private static List<(TryCatchStatement Original, TryCatchStatement Normalized)> NormalizeAdvanceSearch(AstNode root)
    {
        var changed = NormalizeAdvanceValues(root);
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().ToArray())
        {
            if (guarded.GetParent<MethodDeclaration>() is not { } method
                || guarded.TryBlock?.Statements.ToArray() is not [WhileStatement { Condition: PrimitiveExpression { Value: true }, EmbeddedStatement: BlockStatement content }]
                || content.Statements.ToArray() is not [VariableDeclarationStatement advance,
                    ExpressionStatement
                {
                    Expression: AssignmentExpression
                    {
                        Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression carried,
                        Right: ConditionalExpression { Condition: var condition, TrueExpression: var one, FalseExpression: var zero }
                    }
                },
                    IfElseStatement { Condition: var tested, FalseStatement: null, TrueStatement: BlockStatement positive },
                    ExpressionStatement
                {
                    Expression: AssignmentExpression
                    {
                        Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression state,
                        Right: PrimitiveExpression exhausted
                    }
                }, BreakStatement]
                || advance.Variables.ToArray() is not [var flag] || !Name(condition, flag.Name) || !Name(tested, flag.Name)
                || !IntegerConstant(one, 1) || !IntegerConstant(zero, 0)
                || flag.Initializer is not InvocationExpression
                {
                    Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator }
                } move
                || positive.Statements.ToArray() is not [IfElseStatement
                {
                    FalseStatement: null, Condition: var predicate,
                    TrueStatement: BlockStatement { Statements.Count: 1 } rejected
                },
                    ExpressionStatement
                {
                    Expression: AssignmentExpression
                    {
                        Operator: AssignmentOperatorType.Assign,
                        Left: var foundTarget, Right: PrimitiveExpression found
                    }
                }, BreakStatement]
                || rejected.Statements.Single() is not ContinueStatement || !Name(foundTarget, state.Identifier)
                || carried.Identifier == state.Identifier
                || method.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == flag.Name) != 2
                || predicate?.DescendantsAndSelf.OfType<MemberReferenceExpression>().Where(m => m.MemberName == "Current" && Name(m.Target, enumerator.Identifier)).ToArray() is not [var read]
                || CurrentByReference(read)) continue;
            static bool First(Expression? expression, Expression current) => ReferenceEquals(expression, current) || expression switch
            {
                UnaryOperatorExpression { Operator: UnaryOperatorType.Not } unary => First(unary.Expression, current),
                BinaryOperatorExpression binary => First(binary.Left, current),
                CastExpression cast => First(cast.Expression, current),
                _ => FirstReceiver(expression, current),
            };
            if (!First(predicate, read)) continue;
            var names = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name))
                .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
            var item = "current"; for (var suffix = 2; names.Contains(item); suffix++) item = "current" + suffix;
            var labels = method.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            var exit = "enumerationFinished"; for (var suffix = 2; labels.Contains(exit); suffix++) exit = "enumerationFinished" + suffix;
            var matched = (BlockStatement)positive.Clone();
            matched.Descendants.OfType<MemberReferenceExpression>().Single(m => m.MemberName == "Current" && Name(m.Target, enumerator.Identifier)).ReplaceWith(new IdentifierExpression(item));
            matched.Statements.InsertBefore(matched.Statements.First(), new VariableDeclarationStatement(new SimpleType("var"), item, read.Clone()));
            matched.Statements.InsertBefore(matched.Statements.Last(), new ExpressionStatement(new AssignmentExpression(carried.Clone(), one!.Clone())));
            matched.Statements.Last().ReplaceWith(new GotoStatement(exit));
            matched.Statements.Add(new ContinueStatement());
            var body = new BlockStatement {
                new IfElseStatement(move.Clone(), matched),
                new ExpressionStatement(new AssignmentExpression(carried.Clone(), zero!.Clone())),
                new ExpressionStatement(new AssignmentExpression(state.Clone(), exhausted.Clone())),
                new BreakStatement(), new LabelStatement(exit), new BreakStatement() };
            var normalized = (TryCatchStatement)guarded.Clone();
            normalized.TryBlock = new BlockStatement { new WhileStatement(new PrimitiveExpression(true), body) };
            guarded.ReplaceWith(normalized); changed.Add((guarded, normalized));
        }
        return changed;
    }

    private static List<(TryCatchStatement, TryCatchStatement)> NormalizeAdvanceValues(AstNode root)
    {
        var changed = new List<(TryCatchStatement, TryCatchStatement)>();
        static Expression? NumericChoice(Expression? value) => value is CastExpression
        { Type: PrimitiveType { Keyword: "byte" or "sbyte" or "short" or "ushort" or "int" or "uint" or "long" or "ulong" }, Expression: var operand }
                ? NumericChoice(operand) : value is ParenthesizedExpression parentheses ? NumericChoice(parentheses.Expression) : value;
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().ToArray())
        {
            if (guarded.GetParent<MethodDeclaration>() is not { } method
                || guarded.TryBlock?.Statements.LastOrDefault() is not WhileStatement
                { Condition: PrimitiveExpression { Value: true }, EmbeddedStatement: BlockStatement content } loop
                || content.Statements.ToArray() is not [VariableDeclarationStatement advance, VariableDeclarationStatement carried,
                    IfElseStatement { FalseStatement: null, TrueStatement: BlockStatement positive } test,
                    ExpressionStatement
                {
                    Expression: AssignmentExpression
                    {
                        Operator: AssignmentOperatorType.Assign,
                        Left: IdentifierExpression state, Right: var exhausted
                    }
                } empty, BreakStatement]
                || advance.Variables.ToArray() is not [var flag] || carried.Variables.ToArray() is not [var number]
                || !Name(test.Condition, flag.Name) || !IntegerConstant(exhausted, 0)
                || flag.Initializer is not InvocationExpression
                {
                    Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext" }
                } move
                || NumericChoice(number.Initializer) is not ConditionalExpression { Condition: var tested, TrueExpression: var one, FalseExpression: var zero }
                || !Name(tested, flag.Name) || !IntegerConstant(one, 1) || !IntegerConstant(zero, 0)
                || carried.Type is not PrimitiveType { Keyword: "byte" or "sbyte" or "short" or "ushort" or "int" or "uint" or "long" or "ulong" }
                || positive.Descendants.OfType<AssignmentExpression>().Where(a => Name(a.Right, number.Name)).ToArray() is not [var assigned]
                || assigned.Operator != AssignmentOperatorType.Assign || !Name(assigned.Left, state.Identifier)
                || positive.Statements.LastOrDefault() is not (ContinueStatement or BreakStatement)
                || method.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == flag.Name) != 2
                || method.Descendants.OfType<IdentifierExpression>().Count(id => id.Identifier == number.Name) != 1) continue;
            var normalized = (TryCatchStatement)guarded.Clone();
            var matched = (BlockStatement)positive.Clone();
            matched.Descendants.OfType<AssignmentExpression>().Single(a => Name(a.Right, number.Name)).Right = one!.Clone();
            var body = new BlockStatement { new IfElseStatement(move.Clone(), matched), empty.Clone(), new BreakStatement() };
            normalized.TryBlock!.Statements.Last().ReplaceWith(new WhileStatement(loop.Condition!.Clone(), body));
            guarded.ReplaceWith(normalized); changed.Add((guarded, normalized));
        }
        return changed;
    }
}
