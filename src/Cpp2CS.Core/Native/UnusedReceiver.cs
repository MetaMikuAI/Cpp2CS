namespace Cpp2CS.Native;

public static class UnusedReceiver
{
    public static bool Prove(NativeGraph graph)
    {
        if (graph.Problems.Length != 0) return false;
        var visited = new HashSet<ulong>();
        bool Visit(ulong address)
        {
            if (!visited.Add(address)) return false;
            var block = graph.Blocks[address];
            foreach (var instruction in block.Instructions)
            {
                var operands = instruction.Operands;
                static bool Receiver(string? name) => name is "x0" or "w0";
                if (operands.Any(o => Receiver(o.Base) || Receiver(o.Index))) return false;
                var writes = instruction.Mnemonic is "mov" or "adr" or "adrp" or "add" or "sub" or "ldr" or "ldur" or "ldrb" or "ldrh" or "ldrsw";
                if (operands.Skip(writes ? 1 : 0).Any(o => Receiver(o.Register))) return false;
                if (writes && operands.Length > 0 && Receiver(operands[0].Register)) return true;
                if (!(writes || instruction.Mnemonic is "stp" or "str" or "strb" or "strh" or "ldp" or "cmp" or "tst" or "nop" or "b" || NativeGraph.IsConditional(instruction))) return false;
            }
            return block.Successors.Length > 0 && block.Successors.All(Visit);
        }
        return Visit(graph.Entry);
    }
}
