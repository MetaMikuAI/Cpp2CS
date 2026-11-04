using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Machine.Storage;
using Cpp2CS.Ir;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Idioms;

/// <summary>异常暂存栈的 push 后立即 peek：下标相同的栈数组写入与读取之间没有其他写入时，读取即写入的 SSA 值。</summary>
internal static class ExceptionStackValues
{
    /// <summary>
    /// 活动异常栈的 top()：data[size - 1] 的下标是常量的 φ，读取按入边分别取到达的写入，换成值的 φ。
    /// 下标为负的入边上栈是空的，读到的是未定义内容，这条入边上取 0。
    /// </summary>
    public static bool SelectedSlots(MachineFunction function, IFrameCallEffects effects, Func<Variable> fresh)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        ulong? Constant(Variable? variable) => variable is not null && definitions.TryGetValue(variable, out var d) && d.Value is Const c ? c.Value : null;
        FrameModel? model = null;
        var changed = false;
        foreach (var block in function.Blocks)
        {
            var phis = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Define { Value: Load { Width: 64, Address: var address } } load
                    || Scaled(address, definitions) is not var (buffer, index) || !phis.TryGetValue(index, out var phi)
                    || phi.Sources.Any(source => Constant(source) is null)) continue;
                // 从块首到读取之间不能有改变内存的语句。
                if (block.Statements.Take(i).Any(s => s is Store or Call)) continue;
                model ??= new FrameModel(function, effects);
                var sources = new Variable?[phi.Sources.Length];
                var known = true;
                for (var k = 0; k < sources.Length && known; k++)
                {
                    var slot = unchecked((long)Constant(phi.Sources[k])!.Value);
                    if (slot < 0) continue;
                    var predecessor = block.Predecessors[k];
                    var reach = model.Reach(predecessor, predecessor.Statements.Count, buffer + slot * 8, 8);
                    known = reach.Complete && reach.Stores is [{ Value: Use { Width: 64 } use }] && Available(use.Variable, predecessor);
                    if (known) sources[k] = ((Use)reach.Stores[0].Value).Variable;
                }
                if (!known || sources.All(s => s is null)) continue;
                for (var k = 0; k < sources.Length; k++)
                {
                    if (sources[k] is not null) continue;
                    var predecessor = block.Predecessors[k];
                    var undefined = fresh();
                    var at = predecessor.Statements.LastOrDefault() is Jump or Branch ? predecessor.Statements.Count - 1 : predecessor.Statements.Count;
                    predecessor.Statements.Insert(at, new Define(load.Address, undefined, Expr.C(0, 64)));
                    sources[k] = undefined;
                }
                var selected = fresh();
                block.Statements[i] = load with { Value = new Use(selected, 64) };
                block.Statements.Insert(block.Statements.TakeWhile(s => s is Phi).Count(), new Phi(load.Address, selected, sources!));
                changed = true;
                model = null;
                i++;
            }
        }
        return changed;

        bool Available(Variable variable, Block at)
        {
            var dominators = Dominators.Compute(function);
            var home = function.Blocks.FirstOrDefault(b => b.Statements.Any(s => s is Define d && d.Target == variable || s is Phi p && p.Target == variable || s is Call c && c.Defines.Contains(variable)));
            return home is not null && dominators.Dominates(home.Index, at.Index);
        }
    }

    /// <summary>frame + (index &lt;&lt; 3)。</summary>
    private static (long Buffer, Variable Index)? Scaled(Expr address, IReadOnlyDictionary<Variable, Define> definitions)
    {
        Expr Expand(Expr e) => e is Use use && definitions.TryGetValue(use.Variable, out var d) ? Expand(d.Value) : e;
        if (Expand(address) is not Binary { Op: BinOp.Add, Left: var left, Right: var right }) return null;
        return (Expand(left), Expand(right)) is (FrameAddress frame, Binary { Op: BinOp.Shl, Left: Use index, Right: Const { Value: 3 } }) ? (frame.Offset, index.Variable) : null;
    }

    public static bool Run(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        // 读取保留为各自的 SSA 变量：同一位置的两次读取不一定相等。
        Expr Expand(Expr expression) => ExprMap.Map(expression, e => e is Use use && definitions.TryGetValue(use.Variable, out var d)
            && !ExprMap.Walk(d.Value).Any(part => part is Load) ? Expand(d.Value) : null);
        static Expr Strip(Expr value) => value is Convert c ? Strip(c.Operand) : value;
        static Expr Index(Expr value)
        {
            value = Strip(value);
            return value is Binary { Op: BinOp.Sub, Right: Const after } sub
                && Strip(sub.Left) is Binary { Op: BinOp.Add, Right: Const before } add && before.Value == after.Value ? Index(add.Left) : value;
        }
        (long Buffer, Expr Index)? Slot(Expr address) => Expand(address) is Binary
        {
            Op: BinOp.Add, Left: FrameAddress frame,
            Right: Binary { Op: BinOp.Shl, Left: var index, Right: Const { Value: 3 } }
        } ? (frame.Offset, Index(index)) : null;
        // 基址只能作为下标读写的基址出现。
        bool Exposed(Expr expression, long buffer)
        {
            if (expression is Load read && Slot(read.Address) is { } slot && slot.Buffer == buffer) return false;
            return expression is FrameAddress frame ? frame.Offset == buffer : ExprMap.Children(expression).Any(e => Exposed(e, buffer));
        }
        bool Private(long buffer) => !function.Blocks.SelectMany(b => b.Statements).Any(s => s is Store store && Slot(store.Target) is { } slot && slot.Buffer == buffer
            ? Exposed(store.Value, buffer) : ExprMap.Operands(s).Any(e => Exposed(e, buffer)));
        var changed = false;
        var buffers = new HashSet<long>();
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                foreach (var load in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Load>().ToArray())
                {
                    if (load.Width != 64 || Slot(load.Address) is not { } slot || !Private(slot.Buffer)) continue;
                    var current = block;
                    var at = i - 1;
                    Store? push = null;
                    var seen = new HashSet<Block>();
                    var steps = 0;
                    while (push is null && steps < 32 && seen.Add(current))
                    {
                        for (; at >= 0 && push is null; at--, steps++)
                            if (current.Statements[at] is Store store && Slot(store.Target) is { } candidate && candidate.Buffer == slot.Buffer) push = store;
                        if (push is not null || current.Predecessors is not [var previous] || !previous.NormalSuccessors.Contains(current)) break;
                        current = previous;
                        at = current.Statements.Count - 1;
                    }
                    if (push is not { Value.Width: 64 } || Slot(push.Target)!.Value.Index != slot.Index
                        || ExprMap.Walk(push.Value).Any(e => e is Load)) continue;
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
