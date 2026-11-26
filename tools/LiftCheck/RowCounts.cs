using Cpp2CS.Snapshot;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.LiftCheck;

/// <summary>在同一可达指令图上计数按调用槽掩码分块的布局。只枚举块身份，不构造第二份快照。</summary>
internal static class RowCounts
{
    const ulong Arguments = 0x1fful | 1ul << 31 | 0xfful << 32;
    const ulong Results = 3ul | 1ul << 31 | 0xful << 32;
    const ulong Unwind = 3ul | 1ul << 31;

    sealed class Node
    {
        public ulong Use, Kill, Generate, Need;
        public List<(ulong Destination, bool Unwinds)> Edges = [];
    }

    public static (int Split, int Merged) Count(MethodSnapshot snapshot, Arm64Target target,
        LiftLocations locations, ulong entry, bool ordinaryCalls, HashSet<ulong> directTargets)
    {
        // 直接外跳在原布局里按目的地址共用一个调用块。条件外跳在现布局里有零指令的分支臂。
        int merged = snapshot.Blocks.Length + directTargets.Count - locations.Blocks.Values.Count(b => b.Instructions == 0);
        if (!ordinaryCalls || merged == 1) return (merged, merged);
        var nodes = new Dictionary<ulong, Node>();
        foreach (ulong dest in directTargets) nodes.Add(dest, new() { Use = Arguments, Need = Arguments });
        var frame = target.Unwind.Find(entry)!.Value;
        foreach (var (id, (start, length)) in locations.Blocks)
        {
            if (length == 0) continue;
            var node = new Node();
            nodes.Add(start, node);
            var block = snapshot.Flow[id];
            for (int j = 0; j < length; j++)
            {
                ulong pc = start + 4ul * (uint)j;
                var op = target.InstructionAt(pc);
                if (op.IsCall)
                {
                    node.Use |= Arguments & ~node.Kill;
                    node.Generate = Results;
                }
                ulong writes = (ulong)op.WrittenRegisters & Arguments;
                node.Kill |= writes;
                if (!op.IsCall) node.Generate |= writes;
                if (j + 1 != length) continue;
                if (op.Form == Form.BranchRegister && block.Terminator.Kind != TerminatorKind.Switch)
                    node.Use |= Arguments & ~node.Kill;
                ulong dest = op.Destination(pc);
                bool external = (op.Form == Form.Branch || op.Conditional) && (dest < frame.Start || dest >= frame.End);
                if (external) node.Edges.Add((dest, false));
                for (int e = 0; e < block.Terminator.Exits.Length; e++)
                {
                    var exit = block.Terminator.Exits[e];
                    if (exit.Kind != ExitKind.Target || external && e == 0) continue;
                    node.Edges.Add((locations.Blocks[exit.Target].Start, block.Terminator.Kind == TerminatorKind.Invoke && e == 1));
                }
            }
            node.Need = node.Use;
        }
        bool changed;
        var ordered = nodes.Values.Reverse().ToArray();
        do
        {
            changed = false;
            foreach (var node in ordered)
            {
                ulong need = node.Need;
                foreach (var edge in node.Edges) need |= nodes[edge.Destination].Need & ~node.Kill;
                if (need != node.Need) { node.Need = need; changed = true; }
            }
        } while (changed);

        var pending = new Stack<(ulong Pc, ulong Mask)>();
        var seen = new HashSet<(ulong, ulong)>();
        void Visit(ulong pc, ulong mask)
        {
            var key = (pc, mask & nodes[pc].Need);
            if (seen.Add(key)) pending.Push(key);
        }
        Visit(entry, Arguments);
        while (pending.TryPop(out var item))
        {
            var node = nodes[item.Pc];
            ulong after = (item.Mask & ~node.Kill) | node.Generate;
            foreach (var edge in node.Edges) Visit(edge.Destination, edge.Unwinds ? Unwind : after);
        }
        int entryStub = locations.Blocks.ContainsKey(snapshot.Entry) ? 0 : 1;
        return (seen.Count + entryStub, merged);
    }
}
