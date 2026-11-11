namespace Cpp2CS.Native;

/// <summary>块级 Lengauer–Tarjan 支配树；展开调用后的续接段单独成块，段内按语句次序判断。</summary>
internal sealed class Dominance
{
    private readonly int[] pointBlock;
    private readonly int[] enter;
    private readonly int[] leave;

    internal Dominance(NativeFunction function, Dictionary<BlockIdentity, int[]> points, int pointCount)
    {
        pointBlock = new int[pointCount];
        var successors = new List<List<int>> { new() };
        int NewBlock()
        {
            successors.Add([]);
            return successors.Count - 1;
        }
        foreach (var block in function.Blocks.DistinctBy(b => b.Identity))
        {
            var p = points[block.Identity];
            var current = NewBlock();
            pointBlock[p[0]] = current;
            pointBlock[p[1]] = current;
            for (int i = 0; i < block.Statements.Length; i++)
            {
                if (block.Statements[i] is Call call && (call.Unwind is not null || call.DoesNotReturn))
                {
                    var continuation = NewBlock();
                    if (!call.DoesNotReturn) successors[current].Add(continuation);
                    else successors[0].Add(continuation);
                    current = continuation;
                }
                pointBlock[p[i + 2]] = current;
            }
        }
        void Edge(int from, BlockIdentity target)
        {
            if (points.TryGetValue(target, out var p)) successors[from].Add(pointBlock[p[0]]);
        }
        Edge(0, function.Entry);
        foreach (var block in function.Blocks.DistinctBy(b => b.Identity))
        {
            var p = points[block.Identity];
            for (int i = 0; i < block.Statements.Length; i++)
                if (block.Statements[i] is Call { Unwind: { } handler }) Edge(pointBlock[p[i + 1]], handler);
            foreach (var target in ProgramFacts.Targets(block.End)) Edge(pointBlock[p[^1]], target);
        }
        // 不从不可达分量推导跨块支配；仍检查每段内的定义次序。
        var reachable = new bool[successors.Count];
        var pending = new Stack<int>();
        pending.Push(0);
        while (pending.TryPop(out int node))
        {
            if (reachable[node]) continue;
            reachable[node] = true;
            foreach (int child in successors[node]) pending.Push(child);
        }
        foreach (var p in points.Values)
            if (!reachable[pointBlock[p[0]]]) successors[0].Add(pointBlock[p[0]]);
        var parent = ImmediateDominators(successors);
        var children = Enumerable.Range(0, parent.Length).Select(_ => new List<int>()).ToArray();
        for (int i = 1; i < parent.Length; i++) children[parent[i]].Add(i);
        enter = new int[parent.Length];
        leave = new int[parent.Length];
        var traversal = new Stack<(int Node, bool Exit)>();
        traversal.Push((0, false));
        int clock = 0;
        while (traversal.TryPop(out var visit))
        {
            if (visit.Exit)
            {
                leave[visit.Node] = clock++;
                continue;
            }
            enter[visit.Node] = clock++;
            traversal.Push((visit.Node, true));
            foreach (int child in children[visit.Node]) traversal.Push((child, false));
        }
    }

    internal bool Dominates(int definition, int use)
    {
        int a = pointBlock[definition];
        int b = pointBlock[use];
        return a == b ? definition <= use : enter[a] <= enter[b] && leave[b] <= leave[a];
    }

    // DFS 编号与路径压缩均使用显式栈，深循环和长链不占用调用栈。
    private static int[] ImmediateDominators(List<List<int>> graph)
    {
        int count = graph.Count;
        var number = new int[count];
        var vertex = new int[count + 1];
        var parent = new int[count + 1];
        int next = 1;
        number[0] = 1;
        vertex[1] = 0;
        var dfs = new Stack<(int Node, int Child)>();
        dfs.Push((0, 0));
        while (dfs.TryPop(out var frame))
        {
            if (frame.Child == graph[frame.Node].Count) continue;
            dfs.Push((frame.Node, frame.Child + 1));
            int child = graph[frame.Node][frame.Child];
            if (number[child] != 0) continue;
            number[child] = ++next;
            vertex[next] = child;
            parent[next] = number[frame.Node];
            dfs.Push((child, 0));
        }
        var predecessors = Enumerable.Range(0, count + 1).Select(_ => new List<int>()).ToArray();
        for (int i = 0; i < count; i++)
            foreach (int child in graph[i]) predecessors[number[child]].Add(number[i]);
        var semi = Enumerable.Range(0, count + 1).ToArray();
        var label = Enumerable.Range(0, count + 1).ToArray();
        var ancestor = new int[count + 1];
        var idom = new int[count + 1];
        var buckets = Enumerable.Range(0, count + 1).Select(_ => new List<int>()).ToArray();
        var path = new Stack<int>();
        int Evaluate(int v)
        {
            if (ancestor[v] == 0) return label[v];
            int current = v;
            while (ancestor[ancestor[current]] != 0)
            {
                path.Push(current);
                current = ancestor[current];
            }
            while (path.TryPop(out current))
            {
                int above = ancestor[current];
                if (semi[label[above]] < semi[label[current]]) label[current] = label[above];
                ancestor[current] = ancestor[above];
            }
            return label[v];
        }
        for (int w = count; w >= 2; w--)
        {
            foreach (int v in predecessors[w]) semi[w] = Math.Min(semi[w], semi[Evaluate(v)]);
            buckets[semi[w]].Add(w);
            ancestor[w] = parent[w];
            foreach (int v in buckets[parent[w]])
            {
                int u = Evaluate(v);
                idom[v] = semi[u] < semi[v] ? u : parent[w];
            }
            buckets[parent[w]].Clear();
        }
        for (int w = 2; w <= count; w++)
            if (idom[w] != semi[w]) idom[w] = idom[idom[w]];
        var result = new int[count];
        for (int w = 2; w <= count; w++) result[vertex[w]] = vertex[idom[w]];
        return result;
    }
}
