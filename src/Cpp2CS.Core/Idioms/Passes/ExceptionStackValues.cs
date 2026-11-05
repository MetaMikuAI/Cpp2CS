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
        Expr Index(Expr value)
        {
            value = Strip(value);
            if (value is Binary { Op: BinOp.Sub, Right: Const after } sub
                && Strip(sub.Left) is Binary { Op: BinOp.Add, Right: Const before } add && before.Value == after.Value) return Index(add.Left);
            // 长度字段放在栈槽时每次使用都重新读取：同一个槽的读取是同一个下标，前提是两次读取之间没有写它（见下面的回溯）。
            return value is Use use && definitions.TryGetValue(use.Variable, out var read) && Strip(read.Value) is Load { Address: FrameAddress } field ? field : value;
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
        // 固定偏移的写入（长度已知时折叠的 push）也只是写入，不暴露基址。
        bool Private(long buffer) => !function.Blocks.SelectMany(b => b.Statements).Any(s => s is Store store && (Slot(store.Target) is { } slot && slot.Buffer == buffer || store.Target is FrameAddress)
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
                    var stale = false;
                    while (push is null && !stale && steps < 32 && seen.Add(current))
                    {
                        for (; at >= 0 && push is null && !stale; at--, steps++)
                        {
                            if (current.Statements[at] is not Store store) continue;
                            if (Slot(store.Target) is { } candidate && candidate.Buffer == slot.Buffer) push = store;
                            else if (slot.Index is Load { Address: FrameAddress length } && store.Target is FrameAddress written && written.Offset == length.Offset) stale = true;
                        }
                        if (stale) break;
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
        changed |= RemoveUnreadPushes(function, Slot);
        return changed;
    }

    /// <summary>
    /// 活动异常栈的内容只有 top() 才读取；所有读取都换成值或根本没有读取时，push 不再被观察。数组的范围取到它上方第一个被读取的位置。
    /// 下标写入和长度已知时折叠成固定偏移的写入都算 push；top() 的下标是长度减一，基址可能被折叠到更低的地址，也算读取。
    /// </summary>
    private static bool RemoveUnreadPushes(MachineFunction function, Func<Expr, (long Buffer, Expr Index)?> slot, IEnumerable<long>? known = null)
    {
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        IEnumerable<Expr> Observations(Stmt statement) => statement switch
        {
            Store store when slot(store.Target) is not null || store.Target is FrameAddress => [store.Value],
            Call call => [call.Target, .. call.Arguments, .. call.DelegateReceiver is { } receiver ? [receiver] : Array.Empty<Expr>()],
            _ => ExprMap.Operands(statement),
        };
        var observed = statements.SelectMany(Observations).SelectMany(ExprMap.Walk).ToArray();
        var offsets = observed.OfType<FrameAddress>().Select(f => f.Offset).ToHashSet();
        var indexedRoots = observed.OfType<Binary>().Where(b => b is { Op: BinOp.Add, Left: FrameAddress, Right: not Const }).Select(b => ((FrameAddress)b.Left).Offset).ToArray();
        var removed = false;
        HashSet<Block>? normal = null;
        foreach (var buffer in statements.OfType<Store>().Select(s => slot(s.Target)?.Buffer).OfType<long>().Concat(known ?? []).Distinct().ToArray())
        {
            if (offsets.Contains(buffer) || indexedRoots.Any(r => r >= buffer - 16 && r < buffer)) continue;
            var above = offsets.Where(o => o > buffer).DefaultIfEmpty(0).Min();
            bool Written(Store store) => slot(store.Target)?.Buffer == buffer || store.Target is FrameAddress field && field.Offset >= buffer && field.Offset < above;
            var writes = function.Blocks.SelectMany(b => b.Statements.OfType<Store>().Where(Written).Select(s => (Store: s, Block: b))).ToArray();
            // 异常栈的 push 只在 catch 路径上，其余写入是清零长度；其他写法是普通的栈上数组，内容可能被固定偏移读取。
            normal ??= NormalPaths(function);
            if (writes.Any(w => w.Store.Value is not Const && normal.Contains(w.Block))) continue;
            // 跨过上方被读取位置的宽写入，不只是这个数组的内容。
            if (writes.Any(w => w.Store.Target is FrameAddress field && field.Offset + w.Store.Value.Width / 8 > above)) continue;
            foreach (var block in function.Blocks) removed |= block.Statements.RemoveAll(s => s is Store store && Written(store)) > 0;
        }
        return removed;
    }

    /// <summary>从入口不经过落地块就能到达的块。</summary>
    private static HashSet<Block> NormalPaths(MachineFunction function)
    {
        var reached = new HashSet<Block>();
        var pending = new Stack<Block>([function.Blocks[0]]);
        while (pending.TryPop(out var block))
            if (reached.Add(block))
                foreach (var next in block.NormalSuccessors)
                    if (!next.IsLandingPad) pending.Push(next);
        return reached;
    }

    /// <summary>
    /// 活动异常栈的 top()：读取 data[i]，i 沿路径由常量、加减常量和 φ 给出（不同路径上栈深不同）。沿这个网络求出每条到达路径上栈顶的值，读取换成这些值的 φ。
    /// 地址要么直接以数组为基址，要么把 size - 1 的 -1 折叠进基址，两者由 push 写入的基址区分。下标为 -1 的路径上栈是空的，读到的是未定义内容，取 0。
    /// 长度字段可能在栈槽里，所以放在内存提升之后运行。
    /// </summary>
    public static bool TopValues(MachineFunction function, IFrameCallEffects effects, Func<Variable> fresh)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        var phis = function.Blocks.SelectMany(b => b.Statements.OfType<Phi>().Select(p => (Phi: p, Block: b))).ToDictionary(p => p.Phi.Target);
        var dominators = Dominators.Compute(function);
        static Expr Strip(Expr value) => value is Convert c ? Strip(c.Operand) : value;
        Expr Expand(Expr e) => ExprMap.Map(e, v => v is Use use && definitions.TryGetValue(use.Variable, out var d) && !ExprMap.Walk(d.Value).Any(p => p is Load) ? Expand(d.Value) : null);
        // frame + c + (下标 << 3)。
        (long Base, Expr Index)? Scaled(Expr address)
        {
            var terms = TermsPass.Terms(Expand(address)).ToArray();
            var rest = terms.Where(t => t is not Const).ToArray();
            return rest.Length == 2 && rest.OfType<FrameAddress>().ToArray() is [var root]
                && rest.OfType<Binary>().ToArray() is [{ Op: BinOp.Shl, Right: Const { Value: 3 } } shift]
                ? (root.Offset + terms.OfType<Const>().Aggregate(0L, (sum, c) => sum + c.Signed), Strip(shift.Left)) : null;
        }
        (long Buffer, Expr Index)? Pushes(Expr address) => Scaled(address) is var (root, index) ? (root, index) : null;
        var stores = function.Blocks.SelectMany(b => b.Statements).OfType<Store>().ToArray();
        var pushRoots = stores.Select(store => Pushes(store.Target)?.Buffer ?? (store.Target is FrameAddress field ? field.Offset : null)).OfType<long>().ToHashSet();
        FrameModel? model = null;
        var changed = false;
        var buffers = new HashSet<long>();
        foreach (var block in function.Blocks.ToArray())
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Define { Value: Load { Width: 64, Address: var address } } load || Scaled(address) is not var (root, index)) continue;
                // 直接以数组为基址时变量就是下标；基址低一格时变量是 size，下标是它减一。
                long buffer;
                int initial;
                if (pushRoots.Contains(root + 8) && !pushRoots.Contains(root)) (buffer, initial) = (root + 8, -1);
                else if (pushRoots.Contains(root)) (buffer, initial) = (root, 0);
                else continue;
                if (function.Blocks.SelectMany(b => b.Statements).OfType<Call>().SelectMany(c => c.Arguments).SelectMany(ExprMap.Walk).OfType<FrameAddress>().Any(f => f.Offset >= buffer && f.Offset < buffer + 16)) continue;
                model ??= new FrameModel(function, effects);
                var plannedPhis = new List<(Block Block, Phi Phi)>();
                var plannedDefines = new List<(Block Block, Define Define)>();
                var memo = new Dictionary<(Variable, int), Variable?>();
                // 在 at 之前最近一次按 index 下标的 push 写入的值。
                Variable? Pushed(Expr pushedIndex, Block at, int end)
                {
                    var visited = new HashSet<Block>();
                    for (var current = at; current is not null && visited.Add(current); current = current.Predecessors is [var only] ? only : null)
                        for (var k = (ReferenceEquals(current, at) ? end : current.Statements.Count) - 1; k >= 0; k--)
                            if (current.Statements[k] is Store store && Pushes(store.Target) is var (pushRoot, pushIndex) && pushRoot == buffer && pushIndex == pushedIndex)
                                return store.Value is Use { Width: 64 } value ? value.Variable : null;
                    return null;
                }
                // 数组内容的写入。长度和下标按整数运算或常量写入，异常对象不是。
                bool WritesData(Stmt statement) => statement is Store store
                    && (Pushes(store.Target)?.Buffer == buffer || store.Target is FrameAddress field && field.Offset >= buffer && field.Offset < buffer + 72)
                    && Strip(Expand(store.Value)) is not (Const or Binary { Op: BinOp.Add or BinOp.Sub });
                // 从 from 的 φ 之后到 to 的第 end 条语句之前，某条路径上写了数组内容。
                bool WrittenBetween(Block from, Block to, int end)
                {
                    HashSet<Block> Reach(Block start, Block stop, Func<Block, IEnumerable<Block>> next)
                    {
                        var reached = new HashSet<Block>();
                        var pending = new Stack<Block>([start]);
                        while (pending.TryPop(out var current))
                            if (reached.Add(current) && !ReferenceEquals(current, stop))
                                foreach (var following in next(current)) pending.Push(following);
                        return reached;
                    }
                    var on = Reach(from, to, b => b.Successors);
                    on.IntersectWith(Reach(to, from, b => b.Predecessors));
                    return on.Any(b => (ReferenceEquals(b, to) ? b.Statements.Take(end) : b.Statements).Any(WritesData));
                }
                // 下标取 value + delta 时、在 pred 的第 end 条语句之前可用的栈顶值。
                Variable? AtEnd(Expr value, int delta, Block pred, int end, int depth)
                {
                    if (depth > 32) return null;
                    value = Strip(value);
                    // φ 之后又写了数组时，入边上的内容不是这里的栈顶。
                    if (value is Use merged && phis.TryGetValue(merged.Variable, out var merge) && WrittenBetween(merge.Block, pred, end)) return null;
                    switch (value)
                    {
                        case Const constant:
                            {
                                var slot = unchecked((int)constant.Signed) + delta;
                                if (slot is < -1 or > 8) return null;
                                if (slot == -1)
                                {
                                    var undefined = fresh();
                                    plannedDefines.Add((pred, new Define(load.Address, undefined, Expr.C(0, 64))));
                                    return undefined;
                                }
                                // 数组的地址没有传给任何调用，调用改不了它。
                                var reach = model.Reach(pred, end, buffer + slot * 8L, 8, throughCalls: true);
                                return reach is { Complete: true, Stores: [{ Value: Use { Width: 64 } pushed }] } && Defining(pushed.Variable) is { } home && dominators.Dominates(home.Index, pred.Index)
                                    ? pushed.Variable : null;
                            }
                        case Binary { Op: BinOp.Add, Right: Const { Value: 1 } } increment:
                            // 下标正好是这次 push 的位置：值就是 push 写入的值。
                            if (delta == -1 && Pushed(Strip(Expand(increment.Left)), pred, end) is { } written) return written;
                            return AtEnd(increment.Left, delta + 1, pred, end, depth + 1);
                        case Binary { Op: BinOp.Sub, Right: Const { Value: 1 } } decrement:
                            return AtEnd(decrement.Left, delta - 1, pred, end, depth + 1);
                        case Binary { Op: BinOp.Add, Right: Const { Value: 0xffffffff or ulong.MaxValue } } wrapped:
                            return AtEnd(wrapped.Left, delta - 1, pred, end, depth + 1);
                        case Use use when memo.TryGetValue((use.Variable, delta), out var known):
                            return known;
                        case Use use when phis.TryGetValue(use.Variable, out var source):
                            {
                                var top = fresh();
                                memo[(use.Variable, delta)] = top;
                                var sources = new Variable?[source.Phi.Sources.Length];
                                for (var k = 0; k < sources.Length; k++)
                                    if ((sources[k] = AtEnd(new Use(source.Phi.Sources[k], use.Variable.Width), delta, source.Block.Predecessors[k], source.Block.Predecessors[k].Statements.Count, depth + 1)) is null) return memo[(use.Variable, delta)] = null;
                                plannedPhis.Add((source.Block, new Phi(source.Phi.Address, top, sources!)));
                                return top;
                            }
                        case Use use when definitions.TryGetValue(use.Variable, out var definition):
                            return AtEnd(definition.Value, delta, pred, end, depth + 1);
                        default:
                            return null;
                    }
                }
                Block? Defining(Variable variable) => function.Blocks.FirstOrDefault(b => b.Statements.Any(s => s is Define d && d.Target == variable || s is Phi p && p.Target == variable || s is Call c && c.Defines.Contains(variable)));
                if (AtEnd(index, initial, block, i, 0) is not { } value) continue;
                foreach (var (target, define) in plannedDefines)
                    target.Statements.Insert(target.Statements.LastOrDefault() is Jump or Branch or Call ? target.Statements.Count - 1 : target.Statements.Count, define);
                foreach (var (target, phi) in plannedPhis) target.Statements.Insert(0, phi);
                i = block.Statements.IndexOf(load);
                block.Statements[i] = load with { Value = new Use(value, 64) };
                buffers.Add(buffer);
                changed = true;
                model = null;
            }
        // 所有读取换掉之后，长度已知时折叠成固定偏移的 push 就没有下标写入可供识别了，按这里求出的数组删除。
        if (changed) RemoveUnreadPushes(function, address => Pushes(address), buffers);
        return changed;
    }
}
