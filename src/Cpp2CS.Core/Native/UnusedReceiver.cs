using Cpp2CS.Abi;

namespace Cpp2CS.Native;

public static class UnusedReceiver
{
    public static bool Prove(NativeGraph graph, string register = "x0", Func<MachineCall, IEnumerable<string>>? callInputs = null)
    {
        if (graph.Problems.Length != 0) return false;
        register = Arm64Registers.Canonical(register);
        var visited = new HashSet<ulong>();
        var pending = new Stack<ulong>(); pending.Push(graph.Entry);
        while (pending.TryPop(out var address))
        {
            if (!visited.Add(address)) continue;
            var block = graph.Blocks[address];
            var overwritten = false;
            foreach (var instruction in block.Instructions)
            {
                var effect = Arm64Effects.Lower(instruction);
                if (effect.Unsupported is not null || effect.Reads.Contains(register)) return false;
                if (effect.Call is { } call && (callInputs?.Invoke(call) ?? Arm64Registers.CallInputs).Contains(register)) return false;
                if (effect.Writes.Contains(register)) { overwritten = true; break; }
            }
            if (overwritten) continue;
            if (block.Successors.Length == 0) return false;
            foreach (var successor in block.Successors) pending.Push(successor);
        }
        return true;
    }
}
