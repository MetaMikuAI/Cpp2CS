using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Machine.Ssa;



/// <summary>
/// 支配树与支配边界（Cooper–Harvey–Kennedy 迭代算法）。要求 Blocks 按逆后序编号且 Blocks[0] 为入口。
/// </summary>
public sealed class Dominators
{
    private Dominators(int[] idom, List<int>[] children, List<int>[] frontier, int[] preorder, int[] postorder)
    {
        Idom = idom;
        Children = children;
        Frontier = frontier;
        this.preorder = preorder;
        this.postorder = postorder;
    }

    /// <summary>直接支配者的块编号；入口为自身。</summary>
    public int[] Idom { get; }
    public List<int>[] Children { get; }
    public List<int>[] Frontier { get; }
    private readonly int[] preorder;
    private readonly int[] postorder;

    /// <summary>a 支配 b（含 a == b）。</summary>
    public bool Dominates(int a, int b) => preorder[a] <= preorder[b] && postorder[b] <= postorder[a];

    public static Dominators Compute(MachineFunction function)
    {
        var blocks = function.Blocks;
        var count = blocks.Count;
        for (var i = 0; i < count; i++)
            if (blocks[i].Index != i) throw new InvalidOperationException("块编号与逆后序不一致，先调用 Renumber");
        var idom = new int[count];
        Array.Fill(idom, -1);
        idom[0] = 0;
        var changed = true;
        while (changed)
        {
            changed = false;
            for (var b = 1; b < count; b++)
            {
                var candidate = -1;
                foreach (var predecessor in blocks[b].Predecessors)
                {
                    var p = predecessor.Index;
                    if (idom[p] < 0) continue;
                    candidate = candidate < 0 ? p : Intersect(idom, p, candidate);
                }
                if (candidate >= 0 && idom[b] != candidate)
                {
                    idom[b] = candidate;
                    changed = true;
                }
            }
        }

        var children = new List<int>[count];
        for (var i = 0; i < count; i++) children[i] = [];
        for (var b = 1; b < count; b++)
        {
            if (idom[b] < 0) throw new InvalidOperationException($"{blocks[b]} 从入口不可达");
            children[idom[b]].Add(b);
        }

        var frontier = new List<int>[count];
        for (var i = 0; i < count; i++) frontier[i] = [];
        for (var b = 0; b < count; b++)
        {
            var predecessors = blocks[b].Predecessors;
            if (predecessors.Count < 2) continue;
            foreach (var predecessor in predecessors.Select(p => p.Index).Distinct())
            {
                var runner = predecessor;
                while (runner != idom[b])
                {
                    if (!frontier[runner].Contains(b)) frontier[runner].Add(b);
                    if (runner == 0) break;
                    runner = idom[runner];
                }
            }
        }

        // 支配树上的先序/后序编号，用于 O(1) 支配查询
        var preorder = new int[count];
        var postorder = new int[count];
        var stack = new Stack<(int Block, int Next)>();
        stack.Push((0, 0));
        int pre = 0, post = 0;
        preorder[0] = pre++;
        while (stack.Count > 0)
        {
            var (block, next) = stack.Pop();
            if (next < children[block].Count)
            {
                stack.Push((block, next + 1));
                var child = children[block][next];
                preorder[child] = pre++;
                stack.Push((child, 0));
            }
            else postorder[block] = post++;
        }
        return new Dominators(idom, children, frontier, preorder, postorder);
    }

    private static int Intersect(int[] idom, int a, int b)
    {
        while (a != b)
        {
            while (a > b) a = idom[a];
            while (b > a) b = idom[b];
        }
        return a;
    }
}
