using TypeKind = ICSharpCode.Decompiler.TypeSystem.TypeKind;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Extensions.Decompile;

internal sealed partial class RecoveredForeach
{
    private static List<(Statement Read, Statement Previous)> NormalizeCurrentPrefixes(AstNode root)
    {
        var changed = new List<(Statement, Statement)>();
        foreach (var loop in root.Descendants.OfType<WhileStatement>().ToArray())
        {
            if (loop.Condition is not InvocationExpression
                {
                    Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression iterator }
                }
                || loop.EmbeddedStatement is not BlockStatement body) continue;
            var prefix = body.Statements.TakeWhile(PureLocals).ToArray();
            if (prefix.Length == 0 || body.Statements.Skip(prefix.Length).FirstOrDefault() is not VariableDeclarationStatement declaration
                || declaration.Variables.ToArray() is not [var variable] || CurrentRead(variable.Initializer) is not { } read
                || !Name(read.Target, iterator.Identifier) || CurrentByReference(read)
                || loop.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is not { } method
                || !StableCopies(method, prefix, read)) continue;
            declaration.Remove(); body.Statements.InsertBefore(prefix[0], declaration);
            changed.Add((declaration, prefix[^1]));
        }
        return changed;
    }

    private static MemberReferenceExpression? CurrentRead(Expression? expression)
    {
        if (expression is CastExpression cast)
        {
            // object 到引用类型只能是引用转换；不提升可能调用用户运算符的转换。
            if (cast.Expression is not MemberReferenceExpression converted || converted.GetSymbol() is not IProperty { ReturnType.FullName: "System.Object" }
                || cast.Annotation<ResolveResult>()?.Type.IsReferenceType != true) return null;
            expression = converted;
        }
        return expression is MemberReferenceExpression { MemberName: "Current" } read ? read : null;
    }

    // 给首个必求值位置的 Current 建立匹配视图，保留成员读取和转换；未折叠时还原。
    private static List<(VariableDeclarationStatement Declaration, IdentifierExpression Replacement, Expression Original)> NormalizeLeadingCurrent(AstNode root)
    {
        var changed = new List<(VariableDeclarationStatement, IdentifierExpression, Expression)>();
        foreach (var loop in root.Descendants.OfType<WhileStatement>().ToArray())
        {
            if (loop.EmbeddedStatement is not BlockStatement body) continue;
            var condition = loop.Condition;
            if (condition is PrimitiveExpression { Value: true } && body.Statements.FirstOrDefault() is IfElseStatement
                { FalseStatement: null, TrueStatement: BlockStatement positive } test)
            { condition = test.Condition; body = positive; }
            if (condition is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression iterator } }
                || body.Statements.FirstOrDefault() is not { } first
                || first.Descendants.OfType<MemberReferenceExpression>().Where(m => m.MemberName == "Current" && Name(m.Target, iterator.Identifier)).ToArray() is not [var read]
                || CurrentByReference(read)
                || loop.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is not { } method) continue;
            var expression = first switch
            {
                ExpressionStatement
                {
                    Expression: AssignmentExpression
                    {
                        Operator: AssignmentOperatorType.Assign,
                        Left: IdentifierExpression target, Right: var assigned
                    }
                }
                    when target.GetILVariable() is { Type.Kind: not TypeKind.ByReference } => assigned,
                ExpressionStatement statement => statement.Expression,
                YieldReturnStatement statement => statement.Expression,
                IfElseStatement statement => statement.Condition,
                VariableDeclarationStatement initialized when initialized.Variables.ToArray() is [var variable] => variable.Initializer,
                _ => null,
            };
            Expression value = read.Parent is CastExpression converted ? converted : read;
            if (CurrentRead(value) is null || !FirstReceiver(expression, value)
                || first is VariableDeclarationStatement && expression == value) continue;
            var names = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name))
                .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
            var name = "item";
            for (var suffix = 2; names.Contains(name); suffix++) name = "item" + suffix;
            var declaration = new VariableDeclarationStatement(value is CastExpression cast ? cast.Type.Clone() : new SimpleType("var"), name, value.Clone());
            var replacement = new IdentifierExpression(name);
            value.ReplaceWith(replacement);
            body.Statements.InsertBefore(first, declaration);
            changed.Add((declaration, replacement, value));
        }
        return changed;
    }
}
