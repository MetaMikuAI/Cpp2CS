using System.Diagnostics;
using Cpp2CS.Analysis;
using Cpp2CS.Calls;
using Cpp2CS.Facts;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Cpp2CS.Structure;

namespace Cpp2CS.Pipeline;

internal sealed record PreparedSource(ManagedBody Body, (int Rounds, IterationStatus Status) Reduction,
    IReadOnlyList<SourcePass> Passes, IReadOnlyList<string> LibraryEvidence);

/// <summary>逐方法的源码准备；临时变量、模式缓存与日志不跨方法共享。</summary>
internal static class SourcePreparation
{
    public static PreparedSource Run(ManagedBody original, ProgramFacts facts, ManagedTypes types, IMethodSummaries summaries, SourceLibraryIndex index)
    {
        var passes = new List<SourcePass>();
        var reduction = (Rounds: 0, Status: IterationStatus.Stable);
        var body = SourceRewriter.Rewrite(original, types, iteration: result => reduction = (result.Rounds, result.Status), trace: passes.Add);
        var started = Stopwatch.GetTimestamp();
        var library = new SourceLibraryCalls(facts, types, summaries, index);
        var prepared = library.Rewrite(body);
        passes.Add(new("source.library-calls", !ManagedStructure.Same(body, prepared),
            body.Blocks.Sum(b => b.Statements.Count), prepared.Blocks.Sum(b => b.Statements.Count),
            Stopwatch.GetElapsedTime(started).TotalMilliseconds));
        return new(prepared, reduction, passes, library.Evidence.ToArray());
    }
}
