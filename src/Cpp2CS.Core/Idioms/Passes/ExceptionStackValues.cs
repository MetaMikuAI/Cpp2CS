using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Idioms;

/// <summary>异常暂存栈的 push 后立即 peek 使用同一个 SSA 引用，不需要托管堆数组。</summary>
internal static class ExceptionStackValues
{
    public static bool Run(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        Expr Expand(Expr expression) => ExprMap.Map(expression, e => e is Use use && definitions.TryGetValue(use.Variable, out var d) ? Expand(d.Value) : null);
        static Expr Strip(Expr value) => value is Convert c ? Strip(c.Operand) : value;
        (long Buffer, Expr Index)? Slot(Expr address) => address is Binary
        {
            Op: BinOp.Add, Left: FrameAddress frame,
            Right: Binary { Op: BinOp.Shl, Left: var index, Right: Const { Value: 3 } }
        } ? (frame.Offset, Strip(Expand(index))) : null;
        bool Escapes(Expr expression, long buffer, long counter)
        {
            if (expression is Load load && (load.Address is FrameAddress f && f.Offset == counter
                    || Slot(load.Address) is { } slot && slot.Buffer == buffer)) return false;
            if (expression is FrameAddress frame && frame.Offset >= buffer && frame.Offset < counter + 4) return true;
            return ExprMap.Children(expression).Any(e => Escapes(e, buffer, counter));
        }
        bool Private(long buffer, long counter) => !function.Blocks.SelectMany(b => b.Statements).Any(s =>
            s is Store store && (store.Target is FrameAddress f && f.Offset == counter || Slot(store.Target) is { } slot && slot.Buffer == buffer)
                ? Escapes(store.Value, buffer, counter) : ExprMap.Operands(s).Any(e => Escapes(e, buffer, counter)));
        var changed = false;
        var buffers = new HashSet<long>();
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                foreach (var load in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Load>().ToArray())
                {
                    if (load.Width != 64 || Slot(load.Address) is not { } slot
                        || slot.Index is not Binary { Op: BinOp.Sub, Left: var count, Right: Const { Value: 1 } }
                        || Strip(count) is not Load { Width: 32, Address: FrameAddress counter }
                        || counter.Offset <= slot.Buffer || counter.Offset - slot.Buffer > 64 || !Private(slot.Buffer, counter.Offset)) continue;
                    var preceding = new List<Stmt>();
                    var current = block;
                    var at = i - 1;
                    Store? push = null;
                    var seen = new HashSet<Block>();
                    while (preceding.Count < 32 && seen.Add(current))
                    {
                        for (; at >= 0; at--)
                        {
                            var item = current.Statements[at];
                            preceding.Add(item);
                            if (item is Store store && Slot(store.Target) is { } candidate && candidate.Buffer == slot.Buffer)
                            {
                                if (Strip(candidate.Index) == new Load(counter, 32)) push = store;
                                break;
                            }
                        }
                        if (at >= 0 || current.Predecessors is not [var pred] || !pred.NormalSuccessors.Contains(current)) break;
                        current = pred;
                        at = current.Statements.Count - 1;
                    }
                    if (push is null || push.Value.Width != 64) continue;
                    var writes = preceding.OfType<Store>().Where(s => s.Target == counter).ToArray();
                    if (writes is not [var increment]
                        || Strip(Expand(increment.Value)) is not Binary { Op: BinOp.Add, Left: var oldCount, Right: Const { Value: 1 } }
                        || Strip(oldCount) != new Load(counter, 32)) continue;
                    // peek 的计数快照必须位于 ++count 之后，不能沿用 push 前的寄存器。
                    var afterIncrement = preceding.TakeWhile(s => !ReferenceEquals(s, increment)).ToHashSet();
                    bool FreshCount(Expr e)
                    {
                        if (e is Use u && definitions.TryGetValue(u.Variable, out var d))
                            return (!ExprMap.Walk(d.Value).Any(x => x is Load l && l.Address == counter) || afterIncrement.Contains(d)) && FreshCount(d.Value);
                        return ExprMap.Children(e).All(FreshCount);
                    }
                    if (!FreshCount(load.Address)) continue;
                    statement = ExprMap.MapOperands(statement, e => ExprMap.Map(e, part => part == load ? push.Value : null));
                    block.Statements[i] = statement;
                    buffers.Add(slot.Buffer);
                    changed = true;
                }
            }
        foreach (var buffer in buffers)
        {
            var writes = function.Blocks.SelectMany(b => b.Statements).OfType<Store>()
                .Where(s => Slot(s.Target) is { } slot && slot.Buffer == buffer).ToHashSet();
            bool UsesBuffer(Expr e) => ExprMap.Walk(e).OfType<FrameAddress>().Any(f => f.Offset == buffer);
            if (function.Blocks.SelectMany(b => b.Statements).Any(s => s is Store store && writes.Contains(store)
                    ? UsesBuffer(store.Value) : ExprMap.Operands(s).Any(UsesBuffer))) continue;
            foreach (var block in function.Blocks) block.Statements.RemoveAll(s => s is Store store && writes.Contains(store));
        }
        return changed;
    }
}
