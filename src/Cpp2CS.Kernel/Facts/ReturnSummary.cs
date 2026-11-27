using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Facts;

/// <summary>
/// 调用是否返回（设计 7.5）。规格登记之外的两种依据，都只读快照：
///   调用点——这次调用是函数范围里的最后一条指令（快照里块以“不返回”的出口结束）。它返回之后执行的是函数范围之外的字节，
///   不对应生成代码的任何行为；编译器保持语义（设计 16.2），所以有定义的执行里它不返回。
///   被调方法的效果摘要——被调方法的快照里没有返回出口：每条路径都以不返回的调用、陷阱结束，或不终止。
///   由跳转完成的调用带返回出口，所以把调用留给别的函数去返回的方法不在此列。
/// 两者都是关于快照的真命题；回答不了时按会返回处理，只会少结束路径。
/// </summary>
internal static class ReturnSummary
{
    /// <summary>
    /// 这次调用值得去取被调方法的效果摘要：它是块的最后一个出现，块末是单独去往另一个块的出口，或带展开出口的调用。
    /// 不返回的调用之后没有同一条路径上的指令（编译器已经删去），紧跟着的只能是别的块的开头；不满足时不去取摘要，按会返回处理。
    /// </summary>
    public static bool EndsBlock(IFlowGraph graph, OccurrenceId occurrence)
    {
        if (occurrence.Index != graph.OccurrenceCount(occurrence.Block) - 1) return false;
        var terminator = graph.Terminator(occurrence.Block);
        return terminator.Kind == TerminatorKind.Invoke || (terminator.Kind == TerminatorKind.Single && terminator.Exits[0].Kind == ExitKind.Target);
    }

    /// <summary>被调方法的快照里没有返回出口。快照为空（未知）时为假。</summary>
    public static bool NeverReturns(MethodSnapshot? callee)
    {
        if (callee is null) return false;
        foreach (var block in callee.Blocks)
            foreach (var exit in block.Terminator.Exits)
                if (exit.Kind == ExitKind.Return) return false;
        return true;
    }

    /// <summary>这个出现是块的最后一个出现，块以“不返回”的出口结束：这次调用是函数范围里的最后一条指令。</summary>
    public static bool LastInFunction(IFlowGraph graph, OccurrenceId occurrence) =>
        occurrence.Index == graph.OccurrenceCount(occurrence.Block) - 1
        && graph.Terminator(occurrence.Block) is { Kind: TerminatorKind.Single } terminator && terminator.Exits[0].Kind == ExitKind.NoReturn;
}
