using ICSharpCode.Decompiler.CSharp.Syntax;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    // 在匹配视图中统一 try 包住 while 的形态；未成功折叠时还原原 AST。
    private static List<(WhileStatement Loop, TryCatchStatement Original)> NormalizeDirectLoops(AstNode root)
    {
        var changed = new List<(WhileStatement, TryCatchStatement)>();
        foreach (var guarded in root.Descendants.OfType<TryCatchStatement>().ToArray())
        {
            if (guarded.Parent is not BlockStatement || guarded.FinallyBlock is not null
                || guarded.CatchClauses.ToArray() is not [var catcher] || catcher.Condition is not null
                || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || guarded.TryBlock?.Statements.ToArray() is not [WhileStatement { Condition: InvocationExpression { Arguments.Count: 0,
                    Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression enumerator } } advance,
                    EmbeddedStatement: BlockStatement content }]
                || catcher.Body?.Statements.ToArray() is not [var dispose, ThrowStatement thrown]
                || !Dispose(dispose, enumerator.Identifier) || thrown.Expression is not null && !Name(thrown.Expression, catcher.VariableName)) continue;
            // return 或越界跳转原本不会经过正常清理，不能改成隐式 finally。
            var labels = content.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            if (content.Descendants.OfType<ReturnStatement>().Any()
                || content.Descendants.OfType<GotoStatement>().Any(j => j.Label is null || !labels.Contains(j.Label))) continue;
            var body = (BlockStatement)content.Clone();
            body.Statements.Add(new ContinueStatement());
            var test = new TryCatchStatement { TryBlock = new BlockStatement { new IfElseStatement(advance.Clone(), body) } };
            test.CatchClauses.Add((CatchClause)catcher.Clone());
            var loop = new WhileStatement(new PrimitiveExpression(true), new BlockStatement { test, new BreakStatement() });
            guarded.ReplaceWith(loop);
            changed.Add((loop, guarded));
        }
        return changed;
    }
}
