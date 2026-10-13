using System.Collections.Immutable;

namespace Cpp2CS.Native;

public static class NativeParameterAnalysis
{
    public static ImmutableDictionary<ValueId, NativeValue> FindAliases(NativeRegion region) => FindAliases(
        region.Blocks.Select(block => new NativeAnalysisBlock(block.Id, block.Parameters, block.Nodes,
            block.Edges.Where(edge => edge.Target is not null).Select(edge => new NativeAnalysisEdge(edge.Target!.Value, edge.Arguments)).ToImmutableArray())).ToImmutableArray(),
        region.Source.Entries.Select(entry => entry.Block).ToImmutableHashSet());

    public static ImmutableDictionary<ValueId, NativeValue> FindAliases(ImmutableArray<NativeAnalysisBlock> blocks,
        ImmutableHashSet<BlockId> entries)
    {
        var incoming = blocks.ToDictionary(block => block.Id, _ => new List<NativeAnalysisEdge>());
        var definitions = new Dictionary<ValueId, (BlockId Block, bool Parameter)>();
        foreach (var block in blocks)
        {
            foreach (var parameter in block.Parameters) definitions.Add(parameter.Value.Id, (block.Id, true));
            foreach (var node in block.Nodes)
            {
                if (node.Result is { } result) definitions.Add(result.Id, (block.Id, false));
                if (node.Flow is { } flow) definitions.Add(flow.Output.Id, (block.Id, false));
            }
            foreach (var edge in block.Edges)
                if (edge.Target is { } target) incoming[target].Add(edge);
        }

        var candidates = blocks.Where(block => !entries.Contains(block.Id))
            .SelectMany(block => block.Parameters.Select((parameter, index) => (block.Id, parameter.Value, Index: index)))
            .Where(item => item.Value.Type is BitsType).ToArray();
        var indices = candidates.Select((item, index) => (item.Value.Id, index)).ToDictionary(item => item.Id, item => item.index);
        var inputs = new NativeValue[candidates.Length][];
        var dependencies = new int[candidates.Length][];
        var reverse = Enumerable.Range(0, candidates.Length).Select(_ => new List<int>()).ToArray();
        for (var index = 0; index < candidates.Length; index++)
        {
            var candidate = candidates[index];
            inputs[index] = incoming[candidate.Id].Select(edge => edge.Arguments[candidate.Index]).ToArray();
            dependencies[index] = inputs[index].Where(value => indices.ContainsKey(value.Id))
                .Select(value => indices[value.Id]).Distinct().ToArray();
            foreach (var dependency in dependencies[index]) reverse[dependency].Add(index);
        }

        // 依赖图的强连通分量作为整体处理，避免把循环携带的值误当成自身的常量。
        var order = PostOrder(dependencies);
        var componentOf = Enumerable.Repeat(-1, candidates.Length).ToArray();
        var components = new List<List<int>>();
        var pending = new Stack<int>();
        for (var index = order.Count - 1; index >= 0; index--)
        {
            var start = order[index];
            if (componentOf[start] != -1) continue;
            var component = new List<int>();
            var componentIndex = components.Count;
            componentOf[start] = componentIndex;
            pending.Push(start);
            while (pending.TryPop(out var item))
            {
                component.Add(item);
                foreach (var predecessor in reverse[item])
                {
                    if (componentOf[predecessor] != -1) continue;
                    componentOf[predecessor] = componentIndex;
                    pending.Push(predecessor);
                }
            }
            components.Add(component);
        }

        var dominance = new NativeDominance(blocks.Select(block => block.Id),
            blocks.SelectMany(block => block.Edges.Select(edge => (block.Id, edge.Target))), entries);
        var aliases = ImmutableDictionary.CreateBuilder<ValueId, NativeValue>();
        NativeValue Resolve(NativeValue value)
        {
            while (aliases.TryGetValue(value.Id, out var replacement)) value = replacement;
            return value;
        }
        // Kosaraju 的分量顺序与依赖方向一致；逆序使依赖先完成归约。
        for (var componentIndex = components.Count - 1; componentIndex >= 0; componentIndex--)
        {
            var component = components[componentIndex];
            NativeValue? external = null;
            var eligible = true;
            foreach (var index in component)
            {
                if (inputs[index].Length == 0) eligible = false;
                foreach (var input in inputs[index])
                {
                    if (input.Type != candidates[index].Value.Type) eligible = false;
                    if (indices.TryGetValue(input.Id, out var dependency) && componentOf[dependency] == componentIndex) continue;
                    var value = Resolve(input);
                    if (external is { } previous && previous != value) eligible = false;
                    else external = value;
                }
            }
            if (!eligible || external is not { } replacement || !definitions.TryGetValue(replacement.Id, out var definition)) continue;
            foreach (var index in component)
            {
                var candidate = candidates[index];
                if (replacement.Type != candidate.Value.Type || !dominance.Dominates(definition.Block, candidate.Id) ||
                    definition.Block == candidate.Id && !definition.Parameter) eligible = false;
            }
            if (!eligible) continue;
            foreach (var index in component) aliases.Add(candidates[index].Value.Id, replacement);
        }
        return aliases.ToImmutable();
    }

    private static List<int> PostOrder(int[][] edges)
    {
        var visited = new bool[edges.Length];
        var order = new List<int>(edges.Length);
        var stack = new Stack<(int Node, int Next)>();
        for (var root = 0; root < edges.Length; root++)
        {
            if (visited[root]) continue;
            visited[root] = true;
            stack.Push((root, 0));
            while (stack.TryPop(out var frame))
            {
                if (frame.Next == edges[frame.Node].Length) { order.Add(frame.Node); continue; }
                stack.Push((frame.Node, frame.Next + 1));
                var child = edges[frame.Node][frame.Next];
                if (visited[child]) continue;
                visited[child] = true;
                stack.Push((child, 0));
            }
        }
        return order;
    }
}

internal sealed class NativeDominance
{
    private readonly Dictionary<BlockId, int> indices;
    private readonly int[] enter;
    private readonly int[] leave;

    public NativeDominance(NativeRegion region) : this(region.Blocks.Select(block => block.Id),
        region.Blocks.SelectMany(block => block.Edges.Where(edge => edge.Target is not null).Select(edge => (block.Id, edge.Target!.Value))),
        region.Source.Entries.Select(entry => entry.Block)) { }

    public NativeDominance(IEnumerable<BlockId> blocks, IEnumerable<(BlockId Source, BlockId Target)> edges,
        IEnumerable<BlockId> entries)
    {
        indices = blocks.Select((id, index) => (id, index)).ToDictionary(item => item.id, item => item.index);
        var root = indices.Count;
        var successors = Enumerable.Range(0, root + 1).Select(_ => new List<int>()).ToArray();
        var predecessors = Enumerable.Range(0, root + 1).Select(_ => new List<int>()).ToArray();
        foreach (var edge in edges)
        {
            successors[indices[edge.Source]].Add(indices[edge.Target]);
            predecessors[indices[edge.Target]].Add(indices[edge.Source]);
        }
        foreach (var entry in entries.Distinct())
        {
            successors[root].Add(indices[entry]);
            predecessors[indices[entry]].Add(root);
        }

        var visited = new bool[root + 1];
        visited[root] = true;
        var order = new List<int>(root + 1);
        var traversal = new Stack<(int Node, int Next)>();
        traversal.Push((root, 0));
        while (traversal.TryPop(out var frame))
        {
            if (frame.Next == successors[frame.Node].Count) { order.Add(frame.Node); continue; }
            traversal.Push((frame.Node, frame.Next + 1));
            var child = successors[frame.Node][frame.Next];
            if (visited[child]) continue;
            visited[child] = true;
            traversal.Push((child, 0));
        }
        order.Reverse();
        var position = new int[root + 1];
        for (var index = 0; index < order.Count; index++) position[order[index]] = index;
        var immediate = Enumerable.Repeat(-1, root + 1).ToArray();
        immediate[root] = root;
        int Intersect(int first, int second)
        {
            while (first != second)
            {
                while (position[first] > position[second]) first = immediate[first];
                while (position[second] > position[first]) second = immediate[second];
            }
            return first;
        }
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var block in order.Skip(1))
            {
                var parent = -1;
                foreach (var predecessor in predecessors[block])
                {
                    if (immediate[predecessor] == -1) continue;
                    parent = parent == -1 ? predecessor : Intersect(parent, predecessor);
                }
                if (parent == immediate[block]) continue;
                immediate[block] = parent;
                changed = true;
            }
        }

        var children = Enumerable.Range(0, root + 1).Select(_ => new List<int>()).ToArray();
        foreach (var block in order.Skip(1)) children[immediate[block]].Add(block);
        enter = Enumerable.Repeat(-1, root + 1).ToArray();
        leave = Enumerable.Repeat(-1, root + 1).ToArray();
        var clock = 0;
        enter[root] = clock++;
        traversal.Push((root, 0));
        while (traversal.TryPop(out var frame))
        {
            if (frame.Next == children[frame.Node].Count) { leave[frame.Node] = clock++; continue; }
            traversal.Push((frame.Node, frame.Next + 1));
            var child = children[frame.Node][frame.Next];
            enter[child] = clock++;
            traversal.Push((child, 0));
        }
    }

    public bool Dominates(BlockId definition, BlockId use) =>
        indices.TryGetValue(definition, out var source) && indices.TryGetValue(use, out var target) &&
        enter[source] >= 0 && enter[target] >= 0 && enter[source] <= enter[target] && leave[source] >= leave[target];
}
