namespace Cpp2CS.Native;

public sealed record NaturalLoop(ulong Header, HashSet<ulong> Nodes, ulong[] Latches);
public sealed class NaturalLoops
{
    public NaturalLoop[] Loops { get; }
    public ulong[] Order { get; }
    public bool Reducible { get; }
    public NaturalLoops(NativeGraph graph) : this(graph.Entry, graph.Blocks.Values.ToDictionary(b => b.Address, b => b.Successors)) { }
    public NaturalLoops(ulong entry, Dictionary<ulong, ulong[]> successors)
    {
        var graph = new { Entry = entry, Blocks = successors.ToDictionary(p => p.Key, p => new NativeBlock(p.Key, [], p.Value)) };
        var predecessors = graph.Blocks.Keys.ToDictionary(k => k, k => graph.Blocks.Values.Where(b => b.Successors.Contains(k)).Select(b => b.Address).ToArray());
        var dominators = graph.Blocks.Keys.ToDictionary(k => k, k => k == graph.Entry ? new HashSet<ulong> { k } : graph.Blocks.Keys.ToHashSet());
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var key in graph.Blocks.Keys.Where(k => k != graph.Entry))
            {
                var next = graph.Blocks.Keys.ToHashSet();
                foreach (var p in predecessors[key]) next.IntersectWith(dominators[p]);
                next.Add(key);
                if (!next.SetEquals(dominators[key])) { dominators[key] = next; changed = true; }
            }
        }
        var edges = graph.Blocks.Values.SelectMany(b => b.Successors.Where(s => dominators[b.Address].Contains(s)).Select(s => (From: b.Address, To: s))).ToArray();
        Loops = edges.GroupBy(e => e.To).Select(g =>
        {
            var nodes = new HashSet<ulong> { g.Key }; var pending = new Stack<ulong>(g.Select(e => e.From));
            while (pending.TryPop(out var node)) if (nodes.Add(node)) foreach (var p in predecessors[node]) pending.Push(p);
            return new NaturalLoop(g.Key, nodes, g.Select(e => e.From).ToArray());
        }).ToArray();
        var counts = graph.Blocks.Keys.ToDictionary(k => k, k => predecessors[k].Count(p => !edges.Contains((p, k))));
        var ready = new Queue<ulong>(counts.Where(p => p.Value == 0).Select(p => p.Key)); var order = new List<ulong>();
        while (ready.TryDequeue(out var node))
        {
            order.Add(node);
            foreach (var next in graph.Blocks[node].Successors.Where(s => !edges.Contains((node, s)))) if (--counts[next] == 0) ready.Enqueue(next);
        }
        Order = order.ToArray(); Reducible = Order.Length == graph.Blocks.Count;
    }
}
