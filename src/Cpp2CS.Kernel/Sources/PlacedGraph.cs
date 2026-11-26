using System.Collections.Immutable;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Sources;

/// <summary>
/// 图的“取定”视图（设计 7.2）：各行里每一处未定义的占位都换成任意值原子，按（图，块，行，行内序号，树形展开数到的第几处）区分。
/// 内核一律经这个视图读图；此后流动的项不含占位。位置只取决于图的内容。
/// 行的编号：不小于 0 是出现的序号，−1 是终结的条件，−2−e 是第 e 个出口。
/// </summary>
public sealed class PlacedGraph : IFlowGraph
{
    private readonly IFlowGraph inner;
    private readonly ImmutableArray<Term>[][] operands;
    private readonly Terminator[] terminators;

    public PlacedGraph(IFlowGraph graph)
    {
        inner = graph;
        operands = new ImmutableArray<Term>[graph.BlockCount][];
        terminators = new Terminator[graph.BlockCount];
        for (int b = 0; b < graph.BlockCount; b++)
        {
            var block = new BlockId(b);
            int count = graph.OccurrenceCount(block);
            operands[b] = new ImmutableArray<Term>[count];
            for (int i = 0; i < count; i++) operands[b][i] = Row(graph.Operands(new(block, i)), block, i);
            var terminator = graph.Terminator(block);
            Term? condition = terminator.Condition is null ? null : Place(terminator.Condition, block, -1, 0);
            var exits = ImmutableArray.CreateBuilder<Exit>(terminator.Exits.Length);
            for (int e = 0; e < terminator.Exits.Length; e++)
            {
                var exit = terminator.Exits[e];
                var row = Row(exit.Arguments, block, -2 - e);
                exits.Add(exit.Kind switch
                {
                    ExitKind.Target => Exit.To(exit.Target, row.AsSpan()),
                    ExitKind.Return => Exit.Return(row.AsSpan()),
                    _ => exit,
                });
            }
            terminators[b] = terminator.Kind switch
            {
                TerminatorKind.Single => Snapshot.Terminator.Single(exits[0], terminator.Address),
                TerminatorKind.Branch => Snapshot.Terminator.Branch(condition!, exits[0], exits[1], terminator.Address),
                TerminatorKind.Switch => Snapshot.Terminator.Switch(condition!, exits.MoveToImmutable(), terminator.Address),
                _ => Snapshot.Terminator.Invoke(exits[0], exits[1], terminator.Address),
            };
        }
    }

    private ImmutableArray<Term> Row(ImmutableArray<Term> row, BlockId block, int number)
    {
        bool any = false;
        foreach (var term in row) any |= term.HasUndefined;
        if (!any) return row;
        var placed = ImmutableArray.CreateBuilder<Term>(row.Length);
        for (int i = 0; i < row.Length; i++) placed.Add(Place(row[i], block, number, i));
        return placed.MoveToImmutable();
    }

    /// <summary>按树形展开：一个子项被引用两次，其中的占位计两处。</summary>
    private Term Place(Term term, BlockId block, int row, int index)
    {
        if (!term.HasUndefined) return term;
        long leaf = 0;
        Term Go(Term t)
        {
            if (!t.HasUndefined) return t;
            if (t.Kind == TermKind.Undefined) return Terms.Arbitrary(Graph, block, row, index, leaf++, t.Width);
            var parts = new Term[t.Operands.Length];
            for (int i = 0; i < parts.Length; i++) parts[i] = Go(t.Operands[i]);
            return Terms.Rebuild(t, parts);
        }
        return Go(term);
    }

    public int Graph => inner.Graph;
    public TermPool Terms => inner.Terms;
    public int BlockCount => inner.BlockCount;
    public BlockId Entry => inner.Entry;
    public ImmutableArray<Term> EntryParameters => inner.EntryParameters;
    public ImmutableArray<Term> Parameters(BlockId block) => inner.Parameters(block);
    public int OccurrenceCount(BlockId block) => inner.OccurrenceCount(block);
    public IFlowOccurrence Occurrence(OccurrenceId occurrence) => inner.Occurrence(occurrence);
    public ImmutableArray<Term> Operands(OccurrenceId occurrence) => operands[occurrence.Block.Index][occurrence.Index];
    public ImmutableArray<Term> Results(OccurrenceId occurrence) => inner.Results(occurrence);
    public Terminator Terminator(BlockId block) => terminators[block.Index];
}
