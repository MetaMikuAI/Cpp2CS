namespace Cpp2CS.Native;

public sealed record NativeEdge(ulong Source, ulong? Target, string Kind, ExceptionRegion? Region = null);
public sealed record NativeFlowNode(Instruction Instruction, NativeEdge[] Edges, bool Reachable);
public sealed record NativeControlFlow(ulong Entry, NativeFlowNode[] Nodes, ulong[][] Cycles, string[] Problems)
{
    // 指令级控制流保留每个调用的两个出口；循环无需先展开或猜测合流值。
    public static NativeControlFlow Build(Instruction[] instructions, UnwindBoundary boundary, Func<ulong, bool> noReturn)
    {
        var addresses = instructions.Select(i => i.Address).ToHashSet();
        var edges = new Dictionary<ulong, NativeEdge[]>();
        var problems = new List<string>();
        var end = instructions[^1].Address + 4;
        foreach (var i in instructions)
        {
            var outgoing = new List<NativeEdge>();
            void Add(ulong? target, string kind, ExceptionRegion? region = null) => outgoing.Add(new(i.Address, target, kind, region));
            if (NativeGraph.IsConditional(i)) { Add(NativeGraph.Target(i), "taken"); Add(i.Address + 4, "not-taken"); }
            else if (i.Mnemonic == "b") Add(NativeGraph.Target(i), addresses.Contains(NativeGraph.Target(i)) ? "branch" : "tail-call");
            else if (i.Mnemonic == "ret") Add(null, "return");
            else if (i.Mnemonic == "br") Add(null, "indirect-transfer");
            else
            {
                var call = i.Mnemonic is "bl" or "blr";
                if (!(i.Mnemonic == "bl" && noReturn(NativeGraph.Target(i))))
                    Add(i.Address + 4, call ? "normal-return" : "next");
                if (call)
                {
                    var region = boundary.ExceptionRegions.SingleOrDefault(r => r.Start <= i.Address && i.Address < r.End);
                    if (region?.LandingPad is { } pad)
                    {
                        Add(pad, region.ActionOffset == 0 ? "exception-cleanup" : "exception-dispatch", region);
                        if (region.ActionOffset != 0 && !region.Actions.Any(a => a.Kind is "cleanup" or "catch-all"))
                            Add(null, "unmatched-exception-unwind", region);
                    }
                    else Add(null, boundary.Lsda is not null && region is null ? "exception-missing-callsite-terminate" : "exception-unwind", region);
                }
            }
            foreach (var edge in outgoing.Where(e => e.Target.HasValue && e.Kind != "tail-call"))
                if (!addresses.Contains(edge.Target!.Value)) problems.Add($"0x{i.Address:x}: {edge.Kind} 目标 0x{edge.Target:x} 不在函数指令边界");
            edges.Add(i.Address, outgoing.ToArray());
        }
        foreach (var region in boundary.ExceptionRegions)
            if (!addresses.Contains(region.Start) || region.End != end && !addresses.Contains(region.End) ||
                region.LandingPad is { } pad && !addresses.Contains(pad)) problems.Add("LSDA 边界未对齐指令");
        var reachable = new HashSet<ulong>();
        var pending = new Stack<ulong>(); pending.Push(instructions[0].Address);
        while (pending.TryPop(out var pc))
        {
            if (!addresses.Contains(pc) || !reachable.Add(pc)) continue;
            foreach (var edge in edges[pc]) if (edge.Target is { } target && edge.Kind != "tail-call") pending.Push(target);
        }
        var nodes = instructions.Select(i => new NativeFlowNode(i, edges[i.Address], reachable.Contains(i.Address))).ToArray();
        return new(instructions[0].Address, nodes, Components(nodes, reachable), problems.Distinct().ToArray());
    }
    private static ulong[][] Components(NativeFlowNode[] nodes, HashSet<ulong> reachable)
    {
        var graph = nodes.ToDictionary(n => n.Instruction.Address, n => n.Edges.Where(e => e.Target is { } t && reachable.Contains(t)).Select(e => e.Target!.Value).ToArray());
        var indices = new Dictionary<ulong, int>(); var low = new Dictionary<ulong, int>();
        var stack = new Stack<ulong>(); var active = new HashSet<ulong>(); var cycles = new List<ulong[]>();
        void Visit(ulong pc)
        {
            indices[pc] = low[pc] = indices.Count; stack.Push(pc); active.Add(pc);
            foreach (var next in graph[pc])
            {
                if (!indices.ContainsKey(next)) { Visit(next); low[pc] = Math.Min(low[pc], low[next]); }
                else if (active.Contains(next)) low[pc] = Math.Min(low[pc], indices[next]);
            }
            if (low[pc] != indices[pc]) return;
            var component = new List<ulong>();
            ulong item;
            do { item = stack.Pop(); active.Remove(item); component.Add(item); } while (item != pc);
            if (component.Count > 1 || graph[pc].Contains(pc)) cycles.Add(component.Order().ToArray());
        }
        foreach (var pc in reachable.Order()) if (!indices.ContainsKey(pc)) Visit(pc);
        return cycles.OrderBy(c => c[0]).ToArray();
    }
}
