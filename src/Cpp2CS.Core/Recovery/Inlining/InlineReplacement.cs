using System.Collections.Frozen;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>完成区域、活跃值与异常边界检查后的替换计划。应用阶段不再推断语义。</summary>
internal sealed record InlineReplacement(ulong Start, IReadOnlyList<ManagedStatement> Statements, FrozenSet<ulong> Removed,
    IReadOnlyDictionary<(ulong Block, int Index), ManagedStatement>? Rewritten = null)
{
    /// <summary>起点块要并入 try 的区域：替换成的调用可能抛出，而起点块原来不在 try 里。</summary>
    public IReadOnlySet<ManagedRegion> JoinedTry { get; init; } = new HashSet<ManagedRegion>();

    /// <summary>这次替换的证明（<c>inline.proof</c>）。</summary>
    public Cpp2CS.Diagnostics.RuleTrace? Proof { get; init; }

    public ManagedBody Apply(ManagedBody body) => body with
    {
        Blocks = body.Blocks.Where(b => !Removed.Contains(b.Address))
            .Select(b => b.Address == Start ? b with { Statements = Statements } : Rewrite(b)).ToArray(),
        Regions = body.Regions.Select(r => r with
        {
            Try = JoinedTry.Contains(r)
                ? body.Blocks.Select(b => b.Address).Where(a => !Removed.Contains(a) && (a == Start || r.Try.Contains(a))).ToArray()
                : r.Try.Where(a => !Removed.Contains(a)).ToArray(),
            Handler = r.Handler.Where(a => !Removed.Contains(a)).ToArray(),
        }).ToArray(),
    };

    /// <summary>区域之后被替换了子表达式的语句。</summary>
    private ManagedBlock Rewrite(ManagedBlock block) => Rewritten is null || !Rewritten.Keys.Any(k => k.Block == block.Address) ? block : block with
    {
        Statements = block.Statements.Select((s, i) => Rewritten.GetValueOrDefault((block.Address, i), s)).ToArray(),
    };
}
