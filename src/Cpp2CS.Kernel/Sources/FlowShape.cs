using System.Collections.Immutable;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Sources;

/// <summary>
/// 图的形状：各块的入边、逆后序、支配关系、回边与循环头。每张图算一次。
/// 回边按逆后序定义：目标的序号不大于源的序号的边。每个环至少含一条这样的边。
/// </summary>
public sealed class FlowShape
{
    public IFlowGraph Graph { get; }
    private readonly ImmutableArray<EdgeId>[] inEdges;
    private readonly int[] order;          // 块 → 逆后序序号
    private readonly int[] dominator;      // 块 → 直接支配者；入口是它自己
    private readonly bool[] loopHead;

    public FlowShape(IFlowGraph graph)
    {
        Graph = graph;
        int count = graph.BlockCount;
        var incoming = new List<EdgeId>[count];
        for (int b = 0; b < count; b++) incoming[b] = [];
        for (int b = 0; b < count; b++)
        {
            var exits = graph.Terminator(new(b)).Exits;
            for (int e = 0; e < exits.Length; e++)
                if (exits[e].Kind == ExitKind.Target) incoming[exits[e].Target.Index].Add(new(new(b), e));
        }
        inEdges = Array.ConvertAll(incoming, list => list.ToImmutableArray());

        // 逆后序，显式栈。
        var postorder = new List<int>(count);
        var state = new int[count];
        var stack = new Stack<(int Block, int Next)>();
        stack.Push((graph.Entry.Index, 0));
        state[graph.Entry.Index] = 1;
        while (stack.Count > 0)
        {
            var (block, next) = stack.Pop();
            var exits = graph.Terminator(new(block)).Exits;
            bool descended = false;
            for (int e = next; e < exits.Length; e++)
            {
                if (exits[e].Kind != ExitKind.Target) continue;
                int target = exits[e].Target.Index;
                if (state[target] != 0) continue;
                state[target] = 1;
                stack.Push((block, e + 1));
                stack.Push((target, 0));
                descended = true;
                break;
            }
            if (!descended) postorder.Add(block);
        }
        order = new int[count];
        Array.Fill(order, -1);
        var reverse = new int[postorder.Count];
        for (int i = 0; i < postorder.Count; i++)
        {
            int block = postorder[postorder.Count - 1 - i];
            order[block] = i;
            reverse[i] = block;
        }

        // 支配关系：按逆后序迭代求交。
        dominator = new int[count];
        Array.Fill(dominator, -1);
        dominator[graph.Entry.Index] = graph.Entry.Index;
        for (bool changed = true; changed;)
        {
            changed = false;
            for (int i = 1; i < reverse.Length; i++)
            {
                int block = reverse[i], best = -1;
                foreach (var edge in inEdges[block])
                {
                    int source = edge.Source.Index;
                    if (dominator[source] < 0) continue;
                    best = best < 0 ? source : Intersect(source, best);
                }
                if (best >= 0 && dominator[block] != best) { dominator[block] = best; changed = true; }
            }
        }

        loopHead = new bool[count];
        for (int b = 0; b < count; b++)
            foreach (var edge in inEdges[b])
                if (IsBackEdge(edge)) loopHead[b] = true;
    }

    private int Intersect(int a, int b)
    {
        while (a != b)
        {
            while (order[a] > order[b]) a = dominator[a];
            while (order[b] > order[a]) b = dominator[b];
        }
        return a;
    }

    /// <summary>进入某个块的全部边，保留并行边。只在内核里使用：内核之外拿不到入边（设计 7.3）。</summary>
    internal ImmutableArray<EdgeId> InEdges(BlockId block) => inEdges[block.Index];

    public BlockId Target(EdgeId edge) => Graph.Terminator(edge.Source).Exits[edge.Exit].Target;

    public bool IsBackEdge(EdgeId edge) => order[Target(edge).Index] <= order[edge.Source.Index];

    /// <summary>循环头：某条回边的目标。</summary>
    public bool IsLoopHead(BlockId block) => loopHead[block.Index];

    /// <summary>a 是否支配 b（含 a 等于 b）。</summary>
    public bool Dominates(BlockId a, BlockId b)
    {
        int at = b.Index;
        while (true)
        {
            if (at == a.Index) return true;
            int up = dominator[at];
            if (up == at || up < 0) return false;
            at = up;
        }
    }

    /// <summary>直接支配者；入口块没有。</summary>
    public BlockId? ImmediateDominator(BlockId block) =>
        block == Graph.Entry || dominator[block.Index] < 0 ? null : new BlockId(dominator[block.Index]);
}
