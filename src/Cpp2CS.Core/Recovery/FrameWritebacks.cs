using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>按字节追踪栈内快照，只删除值未改变的原位写回；调用和未知写入中断证明。</summary>
internal static class FrameWritebacks
{
    private sealed record ByteValue(Stmt? Origin, int Index, int Constant = -1);

    internal static bool Unread(IEnumerable<Stmt> statements, Store store, Func<Call, int, int?> extent, Func<Call, long, int, bool> noStackRead)
    {
        if (store is not { Target: FrameAddress { Offset: < 0 } frame, Value: Use or Const }
            || store.Value.Width is < 8 or > 128 || frame.Offset + store.Value.Width / 8 > 0) return false;
        return statements.All(s => s is Store { Target: FrameAddress } write
            ? !ExprMap.Walk(write.Value).OfType<FrameAddress>().Any(at => at.Offset < frame.Offset + store.Value.Width / 8)
            : !FrameUses.Touches(s, frame.Offset, store.Value.Width / 8, extent)
                && (s is not Call call || noStackRead(call, frame.Offset, store.Value.Width)));
    }

    internal static int Run(MachineFunction function)
    {
        var values = new Dictionary<Variable, ByteValue[]>();
        var exits = new Dictionary<Block, Dictionary<long, ByteValue>>();
        var removed = 0;
        foreach (var block in function.Blocks)
        {
            var memory = new Dictionary<long, ByteValue>();
            // 未处理的回边或异常入口不继承事实；合流仅保留所有前驱一致的字节。
            if (!block.IsLandingPad && block.Predecessors.Count > 0 && block.Predecessors.All(exits.ContainsKey))
            {
                foreach (var pair in exits[block.Predecessors[0]])
                    if (block.Predecessors.All(p => exits[p].TryGetValue(pair.Key, out var value) && value == pair.Value))
                        memory.Add(pair.Key, pair.Value);
            }
            ByteValue[]? Bytes(Expr expression, Stmt site)
            {
                if (expression.Width is < 8 or > 128 || expression.Width % 8 != 0) return null;
                var size = expression.Width / 8;
                switch (expression)
                {
                    case Const constant:
                        return Enumerable.Range(0, size).Select(i => new ByteValue(null, 0, i < 8 ? (int)(constant.Value >> (i * 8) & 255) : 0)).ToArray();
                    case Use use when values.TryGetValue(use.Variable, out var bytes) && bytes.Length >= size:
                        return bytes[..size];
                    case Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } convert when Bytes(convert.Operand, site) is { } inner:
                        return Enumerable.Range(0, size).Select(i => i < inner.Length ? inner[i] : new ByteValue(null, 0, 0)).ToArray();
                    case Load { Address: FrameAddress { Offset: < 0 } frame } when frame.Offset + size <= 0:
                        return Enumerable.Range(0, size).Select(i =>
                        {
                            var offset = frame.Offset + i;
                            if (!memory.TryGetValue(offset, out var value)) memory[offset] = value = new ByteValue(site, i);
                            return value;
                        }).ToArray();
                    default:
                        return null;
                }
            }
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                switch (statement)
                {
                    case Define define:
                        if (Bytes(define.Value, define) is { } bytes) values[define.Target] = bytes;
                        break;
                    case Store { Target: FrameAddress { Offset: < 0 } frame } store
                        when store.Value.Width is >= 8 and <= 128 && store.Value.Width % 8 == 0 && frame.Offset + store.Value.Width / 8 <= 0:
                        var written = Bytes(store.Value, store);
                        if (written is not null && written.Select((b, at) => memory.TryGetValue(frame.Offset + at, out var old) && old == b).All(equal => equal))
                        {
                            block.Statements[i] = new Nop(store.Address, "栈原值写回");
                            removed++;
                            break;
                        }
                        for (var at = 0; at < store.Value.Width / 8; at++)
                            memory[frame.Offset + at] = written?[at] ?? new ByteValue(store, at);
                        break;
                    case Call or Store or Opaque:
                        memory.Clear();
                        break;
                }
            }
            exits[block] = memory;
        }
        if (removed > 0) Ssa.Propagate.RemoveDead(function);
        return removed;
    }
}
