using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>模板只跨块序中的相邻空跳转；不寻找或重新排列控制流路径。</summary>
internal static class MethodTemplateStatements
{
    public static List<ManagedStatement>? Read(ManagedBody body) => Read(body, out _);
    public static List<ManagedStatement>? Read(ManagedBody body, out string? failure)
    {
        failure = body.Regions.Count != 0 ? "ExceptionRegion" : body.Blocks.Count == 0 ? "EmptyBody" : null;
        if (failure is not null) return null;
        var statements = new List<ManagedStatement>();
        for (int i = 0; i < body.Blocks.Count; i++)
        {
            var block = body.Blocks[i];
            if (i == body.Blocks.Count - 1) statements.AddRange(block.Statements);
            else
            {
                // 只核对块序中的相邻边；不寻找或遍历控制流路径。
                if (block.Statements.LastOrDefault() is not ManagedJump jump || jump.Edge.Copies.Count != 0
                    || jump.Edge.Target != body.Blocks[i + 1].Address)
                { failure = block.Statements.LastOrDefault()?.GetType().Name ?? "ControlFlow"; return null; }
                statements.AddRange(block.Statements.SkipLast(1));
            }
        }
        return statements;
    }
}
