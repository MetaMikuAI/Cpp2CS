using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
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

    // 给已内联的 (T)iterator.Current 建立匹配视图；未恢复为 foreach 时还原原表达式。
    private static List<(VariableDeclarationStatement Declaration, IdentifierExpression Replacement, CastExpression Original)> NormalizeTypedCurrent(AstNode root)
    {
        var changed = new List<(VariableDeclarationStatement, IdentifierExpression, CastExpression)>();
        foreach (var loop in root.Descendants.OfType<WhileStatement>().ToArray())
        {
            if (loop.Condition is not InvocationExpression { Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression iterator } }
                || loop.EmbeddedStatement is not BlockStatement body || body.Statements.FirstOrDefault() is not ExpressionStatement first
                || first.Descendants.OfType<CastExpression>().Where(c => CurrentRead(c) is { Target: var receiver } && Name(receiver, iterator.Identifier)).ToArray() is not [var cast]
                || !FirstReceiver(first.Expression, cast)
                || loop.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is not { } method) continue;
            var names = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name))
                .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
            var name = "item";
            for (var suffix = 2; names.Contains(name); suffix++) name = "item" + suffix;
            var declaration = new VariableDeclarationStatement(cast.Type.Clone(), name, cast.Clone());
            var replacement = new IdentifierExpression(name);
            cast.ReplaceWith(replacement);
            body.Statements.InsertBefore(first, declaration);
            changed.Add((declaration, replacement, cast));
        }
        return changed;
    }
}
