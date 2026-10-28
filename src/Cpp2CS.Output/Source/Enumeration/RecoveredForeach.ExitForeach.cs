using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    // 元素仍写回原局部，保持外部结果和闭包捕获；未恢复的循环还原匹配视图。
    private static List<(VariableDeclarationStatement Read, ExpressionStatement Copy, Expression Original)> NormalizeAssignedCurrent(AstNode root)
    {
        var normalized = new List<(VariableDeclarationStatement, ExpressionStatement, Expression)>();
        foreach (var loop in root.Descendants.OfType<WhileStatement>().ToArray())
        {
            if (loop.Condition is not InvocationExpression { Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } }
                || loop.EmbeddedStatement is not BlockStatement body || body.Statements.FirstOrDefault() is not ExpressionStatement copy
                || copy.Expression is not AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression destination, Right: var value }
                || destination.GetILVariable() is null || CurrentRead(value) is not { Target: var receiver } read
                || !Name(receiver, enumerator.Identifier) || CurrentByReference(read)
                || loop.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is not { } method) continue;
            var names = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name))
                .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
            var name = "item";
            for (var suffix = 2; names.Contains(name); suffix++) name = "item" + suffix;
            var declaration = new VariableDeclarationStatement(value is CastExpression cast ? cast.Type.Clone() : new SimpleType("var"), name, value.Clone());
            value.ReplaceWith(new IdentifierExpression(name));
            body.Statements.InsertBefore(copy, declaration);
            normalized.Add((declaration, copy, value));
        }
        return normalized;
    }

    private static List<Statement>? ExitDisposals(BlockStatement body, AstNode method, BlockStatement parent, TryCatchStatement guarded, string enumerator)
    {
        var internalLabels = body.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
        var jumps = body.Descendants.OfType<GotoStatement>().Where(j => j.Label is null || !internalLabels.Contains(j.Label)).ToArray();
        var statements = parent.Statements.ToArray();
        var result = new List<Statement>();
        foreach (var group in jumps.GroupBy(j => j.Label))
        {
            if (group.Key is null || parent.Statements.OfType<LabelStatement>().Where(l => l.Label == group.Key).ToArray() is not [var label]) return null;
            var index = Array.IndexOf(statements, label);
            // 清理标签不能被正常分支顺落或其他路径跳入，否则移除它会改变释放次数。
            if (index <= Array.IndexOf(statements, guarded) + 1 || index + 1 >= statements.Length
                || statements[index - 1] is not (GotoStatement or ReturnStatement or ThrowStatement)
                || !Dispose(statements[index + 1], enumerator)
                || method.Descendants.OfType<GotoStatement>().Any(j => j.Label == group.Key && !body.Descendants.Contains(j))) return null;
            result.Add(statements[index + 1]);
        }
        return result;
    }
}
