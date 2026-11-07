using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// IL 只能从 try 的第一条指令进入。原生代码没有这个限制：状态机的分派被线程化后，会直接跳到 try 中间的恢复点。
/// 这里把多个入口收拢成 try 开头的分派块：从外部进入的边先写入口序号，再由分派块跳到原来的目标。
/// 分派块只读刚写入的局部，不会抛出，放进 try 不改变异常语义。
/// </summary>
internal static class ExceptionEntries
{
    /// <summary>分派块的地址不对应原生代码，取高位以免与原生块重合。</summary>
    private const ulong SyntheticAddress = 1UL << 63;
    private const ulong NativeAddressMask = (1UL << 48) - 1;

    /// <summary>这个地址是分派块。其他步骤新建的块用不同的高位。</summary>
    public static bool IsDispatch(ulong address) => address >> 62 == 2;

    public static ManagedBody Run(ManagedBody body, Func<LocalValue> newLocal)
    {
        var count = 0UL;
        // 从内向外：外层可能因此以内层的分派块作为入口，再次收拢时结构不变。
        // 次序在开始前定下：收拢内层后，外层的成员会多出分派块。
        foreach (var i in Enumerable.Range(0, body.Regions.Count).OrderBy(i => body.Regions[i].Try.Count).ToArray())
        {
            // 开头可能已经是内层的分派块，只取原生地址部分，编号才不会重叠。
            var address = SyntheticAddress | count << 48 | body.Regions[i].Try[0] & NativeAddressMask;
            if (Collapse(body, body.Regions[i], address, newLocal) is not { } collapsed) continue;
            body = collapsed;
            count++;
        }
        return body;
    }

    private static ManagedBody? Collapse(ManagedBody body, ManagedRegion region, ulong address, Func<LocalValue> newLocal)
    {
        var members = region.Try.ToHashSet();
        var first = region.Try[0];
        var outside = body.Blocks.Where(b => !members.Contains(b.Address)).SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges)
            .Select(e => e.Target).Where(members.Contains).Distinct().ToList();
        // 方法入口也是一个入口。局部初值为 0，所以它固定是第 0 项。
        var method = body.Blocks[0].Address;
        if (members.Contains(method)) { outside.Remove(method); outside.Insert(0, method); }
        if (outside.Count == 0 || outside is [var only] && only == first) return null;
        var index = newLocal();
        var cases = outside.Select((target, i) => (target, i)).ToDictionary(p => p.target, p => p.i);
        var copy = (int i) => new ManagedCopy(index, new ConstantValue((ulong)i, index.Type, index.Width));
        ManagedEdge Enter(ManagedEdge edge) => cases.TryGetValue(edge.Target, out var i)
            ? new ManagedEdge(address, [.. edge.Copies, copy(i)]) : edge;
        var blocks = body.Blocks.Select(b => members.Contains(b.Address) ? b
            : b with { Statements = b.Statements.Select(s => ManagedValues.MapEdges(s, Enter)).ToArray() }).ToList();
        ManagedStatement dispatch = outside is [var single]
            ? new ManagedJump(single, new ManagedEdge(single, []))
            : new ManagedSwitch(outside[0], index, outside.Select(t => new ManagedEdge(t, [])).ToArray());
        blocks.Insert(blocks.FindIndex(b => b.Address == first), new ManagedBlock(address, [dispatch]));
        // 分派块属于这个 try，也属于包含它的区域。
        IReadOnlyList<ulong> Extend(IReadOnlyList<ulong> list)
        {
            var at = list.ToList().IndexOf(first);
            return at < 0 ? list : [.. list.Take(at), address, .. list.Skip(at)];
        }
        return body with
        {
            Blocks = blocks,
            Regions = body.Regions.Select(r => r with { Try = Extend(r.Try), Handler = Extend(r.Handler) }).ToArray(),
        };
    }
}
