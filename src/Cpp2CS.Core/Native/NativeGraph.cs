namespace Cpp2CS.Native;

public sealed record NativeBlock(ulong Address, Instruction[] Instructions, ulong[] Successors);
public sealed class NativeGraph
{
    public Dictionary<ulong, NativeBlock> Blocks { get; }
    public ulong Entry { get; }
    public string[] Problems { get; }
    public NativeGraph(Instruction[] instructions, Func<ulong, bool> noReturn, Func<ulong, bool>? knownTailCall = null, ulong[]? boundaries = null)
    {
        Entry = instructions[0].Address;
        var end = instructions[^1].Address + 4;
        bool Tail(Instruction i) => i.Mnemonic == "b" && (Target(i) < Entry || Target(i) >= end) && knownTailCall?.Invoke(Target(i)) == true;
        var leaders = new HashSet<ulong> { Entry };
        leaders.UnionWith(boundaries ?? []);
        foreach (var i in instructions)
        {
            if (IsConditional(i) || i.Mnemonic == "b") leaders.Add(Target(i));
            if (IsConditional(i) || i.Mnemonic is "b" or "br" or "ret" || i.Mnemonic == "bl" && noReturn(Target(i)))
                if (i.Address + 4 < end) leaders.Add(i.Address + 4);
        }
        var blocks = new Dictionary<ulong, NativeBlock>();
        var current = new List<Instruction>();
        foreach (var i in instructions)
        {
            if (leaders.Contains(i.Address) && current.Count > 0) { Add(); current.Clear(); }
            current.Add(i);
        }
        if (current.Count > 0) Add();
        void Add()
        {
            var last = current[^1];
            ulong[] successors = IsConditional(last) ? [Target(last), last.Address + 4] : Tail(last) ? [] : last.Mnemonic == "b" ? [Target(last)] :
                last.Mnemonic is "ret" or "br" || last.Mnemonic == "bl" && noReturn(Target(last)) ? [] : [last.Address + 4];
            blocks.Add(current[0].Address, new(current[0].Address, current.ToArray(), successors));
        }
        var reachable = new HashSet<ulong>(); var pending = new Queue<ulong>(); pending.Enqueue(Entry);
        var problems = new List<string>();
        while (pending.TryDequeue(out var address))
        {
            if (!reachable.Add(address)) continue;
            var block = blocks[address];
            foreach (var next in block.Successors)
            {
                if (blocks.ContainsKey(next)) { pending.Enqueue(next); continue; }
                var last = block.Instructions[^1];
                var edge = last.Mnemonic == "bl" ? "调用返回" : next == last.Address + 4 && last.Mnemonic != "b" ? "顺序执行" : "分支";
                var hint = last.Mnemonic == "bl" ? $"；请核对被调函数 0x{Target(last):x} 的不返回属性及函数边界" : "；请核对函数边界及外部跳转类型";
                problems.Add($"0x{last.Address:x}: {edge}边指向 0x{next:x}，不在函数指令范围 [0x{Entry:x}, 0x{end:x}){hint}");
            }
        }
        Blocks = blocks.Where(k => reachable.Contains(k.Key)).ToDictionary();
        Problems = problems.ToArray();
    }
    public static bool IsConditional(Instruction i) => i.Mnemonic.StartsWith("b.") || i.Mnemonic is "cbz" or "cbnz" or "tbz" or "tbnz";
    public static ulong Target(Instruction i) => checked((ulong)i.Operands.Last(p => p.Kind == 2).Immediate);
    public ulong[]? TopologicalOrder()
    {
        if (Problems.Length > 0) return null;
        var counts = Blocks.Keys.ToDictionary(k => k, _ => 0);
        foreach (var block in Blocks.Values) foreach (var next in block.Successors) counts[next]++;
        var ready = new Queue<ulong>(counts.Where(k => k.Value == 0).Select(k => k.Key));
        var output = new List<ulong>();
        while (ready.TryDequeue(out var address))
        {
            output.Add(address);
            foreach (var next in Blocks[address].Successors) if (--counts[next] == 0) ready.Enqueue(next);
        }
        return output.Count == Blocks.Count ? output.ToArray() : null;
    }
}
