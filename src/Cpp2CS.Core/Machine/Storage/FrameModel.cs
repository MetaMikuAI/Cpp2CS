using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Machine.Storage;

/// <summary>调用对一个实参的使用。Size 为 -1 时范围未知；Retained 表示地址在调用之后仍可能被使用。</summary>
internal readonly record struct ArgumentUse(int Size, MemoryAccess Access, bool Retained)
{
    public static readonly ArgumentUse Unknown = new(-1, MemoryAccess.ReadWrite, true);
    public static readonly ArgumentUse None = new(0, MemoryAccess.None, false);
}

/// <summary>调用对帧内存的影响，随调用目标的确定而变精确。</summary>
internal interface IFrameCallEffects
{
    ArgumentUse Argument(Call call, int index);
    /// <summary>调用可能经已逃逸的地址写入。</summary>
    bool WritesEscaped(Call call);
    /// <summary>调用从栈上读取的实参字节数；未知时为 null。</summary>
    int? StackRead(Call call);
}

/// <summary>程序点上某段帧内存的来源。Complete 时每条路径都到达 Stores 中的完整写入。</summary>
internal sealed record FrameReach(IReadOnlyList<Store> Stores, bool FromEntry, Stmt? Clobber, bool Exhausted)
{
    public bool Complete => !FromEntry && Clobber is null && !Exhausted && Stores.Count > 0;
}

/// <summary>
/// 方法的固定帧内存模型。地址按流不敏感的指向关系解析（经寄存器、私有栈槽、常量偏移与选择传递），
/// 动态分配的区域不覆盖固定帧。地址的使用分为直接访问、调用的有界访问与逃逸；逃逸的地址可访问其上方的整段内存，
/// 除非签名给出长度。各规则通过这里的查询判断“这里存的是什么、谁能看到”，不再各写一份。
/// 调用后再读取实参区的值不属于 clang 的生成形态，因此 SP 记录本身不算访问。
/// </summary>
internal sealed class FrameModel
{
    private const int ReachBudget = 8192;

    private readonly record struct CallRange(long Offset, int Size, MemoryAccess Access);

    private readonly MachineFunction function;
    private readonly IFrameCallEffects calls;
    private readonly Dictionary<Variable, Expr> definitions = [];
    private readonly Dictionary<Variable, HashSet<long>> pointsTo = [];
    private readonly Dictionary<long, HashSet<long>> held = [];
    /// <summary>以帧地址为基址、加变量下标得到的地址：只在作为读写地址时不算逃逸。</summary>
    private readonly Dictionary<Variable, HashSet<long>> indexed = [];
    private readonly HashSet<long> loaded = [];
    private readonly Dictionary<Call, List<CallRange>> ranges = new(ReferenceEqualityComparer.Instance);
    private readonly List<(long Offset, int? Size)> escaped = [];

    public FrameModel(MachineFunction function, IFrameCallEffects calls)
    {
        this.function = function;
        this.calls = calls;
        foreach (var statement in function.Blocks.SelectMany(b => b.Statements))
            if (statement is Define define) definitions[define.Target] = define.Value;
        SolvePointers();
        foreach (var statement in function.Blocks.SelectMany(b => b.Statements)) Collect(statement);
        SolveEscapes();
    }

    /// <summary>地址可能指向的帧偏移；不指向固定帧时为空。</summary>
    public IReadOnlyCollection<long> Targets(Expr address) => Points(address).Distinct().ToArray();

    /// <summary>地址唯一指向的帧偏移。</summary>
    public long? Slot(Expr address) => Targets(address) is { Count: 1 } targets ? targets.First() : null;

    public bool Escaped(long offset, int bytes) => escaped.Any(e => Overlaps(e.Offset, e.Size, offset, bytes));

    /// <summary>
    /// 区间不再被读取，地址未逃逸，调用也不经指针观察它。没有被直接读取过的槽可能是未解析调用的栈实参，因此要求调用不读这段栈；
    /// 被读取过的槽是私有保存，不在实参区。
    /// </summary>
    public bool Unobserved(long offset, int bytes)
    {
        if (Escaped(offset, bytes)) return false;
        var spilled = loaded.Any(l => l >= offset && l < offset + bytes);
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (ranges.TryGetValue(call, out var used) && used.Any(r => Overlaps(r.Offset, r.Size < 0 ? null : r.Size, offset, bytes))) return false;
            if (!spilled && ReadsOnStack(call, offset, bytes)) return false;
        }
        return function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Load>()
            .All(load => !Points(load.Address).Any(at => at < offset + bytes && offset < at + load.Width / 8)
                && !IndexedRoots(load.Address).Any(root => root < offset + bytes));
    }

    /// <summary>第 index 条语句之前，[offset, offset+bytes) 的来源。throughCalls：已知调用不改写它，只看写入。</summary>
    public FrameReach Reach(Block block, int index, long offset, int bytes, bool throughCalls = false)
    {
        var stores = new List<Store>();
        var fromEntry = false;
        var steps = 0;
        var visited = new HashSet<Block>();
        var pending = new Stack<(Block Block, int End)>();
        pending.Push((block, index));
        while (pending.TryPop(out var current))
        {
            var stopped = false;
            for (var i = current.End - 1; i >= 0 && !stopped; i--)
            {
                if (++steps > ReachBudget) return new(stores, fromEntry, null, true);
                var statement = current.Block.Statements[i];
                if ((!throughCalls || statement is not Call) && Kill(statement, offset, bytes, out var store))
                {
                    if (store is null) return new(stores, fromEntry, statement, false);
                    if (!stores.Contains(store)) stores.Add(store);
                    stopped = true;
                }
            }
            if (stopped) continue;
            if (current.Block == function.EntryBlock) fromEntry = true;
            foreach (var predecessor in current.Block.Predecessors)
                if (visited.Add(predecessor)) pending.Push((predecessor, predecessor.Statements.Count));
        }
        return new(stores, fromEntry, null, false);
    }

    private bool Kill(Stmt statement, long offset, int bytes, out Store? definite)
    {
        definite = null;
        switch (statement)
        {
            case Store store:
                {
                    var targets = Targets(store.Target);
                    var width = store.Value.Width / 8;
                    if (targets.Count == 0)
                    {
                        var ceiling = IndexCeiling(store.Target, 0);
                        return IndexedRoots(store.Target).Any(root => Overlaps(root, ceiling is { } end && end > root ? checked((int)(end - root)) : null, offset, bytes))
                            || Escaped(offset, bytes);
                    }
                    if (targets.Count == 1 && targets.First() <= offset && targets.First() + width >= offset + bytes)
                    {
                        definite = store;
                        return true;
                    }
                    return targets.Any(t => Overlaps(t, width, offset, bytes));
                }
            case Call call:
                if (ranges.TryGetValue(call, out var used)
                    && used.Any(r => (r.Access & MemoryAccess.Write) != 0 && Overlaps(r.Offset, r.Size < 0 ? null : r.Size, offset, bytes))) return true;
                return calls.WritesEscaped(call) && Escaped(offset, bytes);
            case Opaque:
                return true;
            default:
                return false;
        }
    }

    private static bool Overlaps(long start, int? size, long offset, int bytes) =>
        start < offset + bytes && (size is null || offset < start + size);

    // ---- 指向关系 ----

    private void SolvePointers()
    {
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var statement in statements)
                switch (statement)
                {
                    case Define { Target.Width: 64 } define:
                        changed |= Add(pointsTo, define.Target, Points(define.Value));
                        changed |= Add(indexed, define.Target, IndexedRoots(define.Value));
                        break;
                    case Phi { Target.Width: 64 } phi:
                        foreach (var source in phi.Sources)
                            if (pointsTo.TryGetValue(source, out var incoming)) changed |= Add(pointsTo, phi.Target, incoming.ToArray());
                        break;
                    case Store { Value.Width: 64 } store:
                        var values = Points(store.Value).ToArray();
                        if (values.Length > 0)
                            foreach (var slot in Points(store.Target).ToArray()) changed |= Add(held, slot, values);
                        break;
                }
        }
    }

    private static bool Add<TKey>(Dictionary<TKey, HashSet<long>> sets, TKey key, IEnumerable<long> values) where TKey : notnull
    {
        var changed = false;
        foreach (var value in values)
        {
            if (!sets.TryGetValue(key, out var set)) sets[key] = set = [];
            changed |= set.Add(value);
        }
        return changed;
    }

    private IEnumerable<long> Points(Expr expression) => expression switch
    {
        FrameAddress frame => [frame.Offset],
        Use { Width: 64 } use => pointsTo.TryGetValue(use.Variable, out var set) ? set : [],
        Binary { Op: BinOp.Add, Right: Const c } add => Points(add.Left).Select(o => o + c.Signed),
        Binary { Op: BinOp.Add, Left: Const c } add => Points(add.Right).Select(o => o + c.Signed),
        Binary { Op: BinOp.Sub, Right: Const c } sub => Points(sub.Left).Select(o => o - c.Signed),
        Select select => Points(select.True).Concat(Points(select.False)),
        Load { Width: 64 } load => Points(load.Address).SelectMany(s => held.TryGetValue(s, out var values) ? values : []),
        _ => [],
    };

    /// <summary>帧地址加变量下标的基址；下标范围未知，访问按基址以上的任意位置计。</summary>
    private IEnumerable<long> IndexedRoots(Expr expression) => expression switch
    {
        Use { Width: 64 } use => indexed.TryGetValue(use.Variable, out var set) ? set : [],
        Binary { Op: BinOp.Add, Right: not Const } add when Points(add.Left).Any() && !Points(add.Right).Any() => Points(add.Left),
        Binary { Op: BinOp.Add, Left: not Const } add when Points(add.Right).Any() && !Points(add.Left).Any() => Points(add.Right),
        _ => [],
    };

    /// <summary>下标取自帧上的计数槽时，数组止于该槽：计数不会是数组自身的元素。</summary>
    private long? IndexCeiling(Expr expression, int depth)
    {
        if (depth > 8) return null;
        if (expression is Load load) return Slot(load.Address);
        if (expression is Use use) return definitions.TryGetValue(use.Variable, out var value) ? IndexCeiling(value, depth + 1) : null;
        long? lowest = null;
        foreach (var child in ExprMap.Children(expression))
            if (IndexCeiling(child, depth + 1) is { } at) lowest = lowest is { } known ? Math.Min(known, at) : at;
        return lowest;
    }

    /// <summary>向下的动态分配：起点减去按 16 字节对齐的 32 位无符号大小。结果位于起点之下，不覆盖固定帧。</summary>
    private bool DynamicAllocation(Expr expression, out Expr? size)
    {
        size = null;
        if (expression is not Binary { Op: BinOp.Sub } sub) return false;
        var aligned = Local(sub.Right);
        if (aligned is not Binary { Op: BinOp.And, Right: Const { Value: 0x1fffffff0 or 0xfffffffffffffff0 } } mask
            || Local(mask.Left) is not Binary { Op: BinOp.Add, Right: Const { Value: 15 } } padded
            || Local(padded.Left) is not Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 64, Operand.Width: 32 }) return false;
        size = sub.Right;
        return true;
    }

    private Expr Local(Expr expression) => expression is Use use && definitions.TryGetValue(use.Variable, out var value) ? value : expression;

    // ---- 使用 ----

    private void Collect(Stmt statement)
    {
        switch (statement)
        {
            case Define define:
                Walk(define.Value, false);
                break;
            case Phi:
                break;
            case Store store:
                {
                    var direct = Points(store.Target).Any();
                    if (IndexedRoots(store.Target).Any()) WalkIndex(store.Target);
                    else if (!direct) Walk(store.Target, true);
                    // 经下标写入帧的地址按存入不可追踪的位置处理。
                    Walk(store.Value, !direct);
                    break;
                }
            case Call call:
                Walk(call.Target, true);
                if (call.DelegateReceiver is { } receiver) Walk(receiver, true);
                for (var i = 0; i < call.Arguments.Length; i++)
                {
                    var targets = Targets(call.Arguments[i]);
                    if (targets.Count == 0) { Walk(call.Arguments[i], true); continue; }
                    var use = calls.Argument(call, i);
                    if (!ranges.TryGetValue(call, out var used)) ranges[call] = used = [];
                    foreach (var target in targets)
                    {
                        if (use.Retained) escaped.Add((target, use.Size < 0 ? null : use.Size));
                        else if (use.Access != MemoryAccess.None) used.Add(new(target, use.Size, use.Access));
                    }
                    Walk(call.Arguments[i], false);
                }
                break;
            default:
                foreach (var operand in ExprMap.Operands(statement)) Walk(operand, true);
                break;
        }
    }

    /// <summary>consumed 表示这个值不再只是地址的搬运：其中的帧地址就此逃逸。</summary>
    private void Walk(Expr expression, bool consumed)
    {
        switch (expression)
        {
            case Load load:
                if (Points(load.Address).Any())
                {
                    foreach (var at in Points(load.Address)) loaded.Add(at);
                    if (consumed) Escape(load);
                }
                else if (IndexedRoots(load.Address).Any()) WalkIndex(load.Address);
                else Walk(load.Address, true);
                break;
            case FrameAddress or Use:
                if (consumed) Escape(expression);
                break;
            case Binary when !consumed && IndexedRoots(expression).Any():
                WalkIndex(expression);
                break;
            case Binary { Op: BinOp.Add or BinOp.Sub, Right: Const } offset:
                Walk(offset.Left, consumed);
                break;
            case Binary { Op: BinOp.Add, Left: Const } offset:
                Walk(offset.Right, consumed);
                break;
            case Select select:
                Walk(select.Condition, true);
                Walk(select.True, consumed);
                Walk(select.False, consumed);
                break;
            case Compare compare:
                Walk(compare.Left, false);
                Walk(compare.Right, false);
                break;
            case not null when DynamicAllocation(expression, out var size):
                Walk(size!, true);
                break;
            default:
                foreach (var child in ExprMap.Children(expression!)) Walk(child, true);
                break;
        }
    }

    /// <summary>下标地址只检查下标本身。</summary>
    private void WalkIndex(Expr address)
    {
        if (address is not Binary { Op: BinOp.Add } add) return;
        Walk(Points(add.Left).Any() ? add.Right : add.Left, true);
    }

    private void Escape(Expr expression)
    {
        foreach (var target in Points(expression).Concat(IndexedRoots(expression))) escaped.Add((target, null));
    }

    private bool ReadsOnStack(Call call, long offset, int bytes)
    {
        if (call.StackPointer is not { } pointer || Slot(pointer) is not { } sp || offset + bytes <= sp) return false;
        return calls.StackRead(call) is not { } read || offset < sp + read;
    }

    /// <summary>栈槽中的地址：槽本身可被观察，或可能作为未读取的栈实参传出时，其中的地址也逃逸。</summary>
    private void SolveEscapes()
    {
        var statements = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().ToArray();
        var done = new HashSet<long>();
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var (slot, values) in held)
            {
                if (done.Contains(slot)) continue;
                var observed = Escaped(slot, 8) || !loaded.Contains(slot) && statements.Any(c => ReadsOnStack(c, slot, 8))
                    || ranges.Values.Any(used => used.Any(r => Overlaps(r.Offset, r.Size < 0 ? null : r.Size, slot, 8)));
                if (!observed) continue;
                done.Add(slot);
                foreach (var value in values) escaped.Add((value, null));
                changed = true;
            }
        }
    }
}

/// <summary>私有帧内存的转发：读取在每条路径上都来自同值的完整写入时，改写为该值；不再被观察的写入随之删除。</summary>
internal static class FrameForwarding
{
    private const int Rounds = 8;

    public static bool Run(MachineFunction function, IFrameCallEffects calls)
    {
        var any = false;
        for (var round = 0; round < Rounds; round++)
        {
            var model = new FrameModel(function, calls);
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var statement = block.Statements[i];
                    if (!ExprMap.Operands(statement).SelectMany(ExprMap.Walk).Any(e => e is Load)) continue;
                    var index = i;
                    var forwarded = false;
                    var rewritten = ExprMap.MapOperands(statement, operand => Fold.Simplify(ExprMap.Map(operand, e =>
                    {
                        if (e is not Load load || Forward(model, block, index, load) is not { } value) return null;
                        forwarded = true;
                        return value;
                    })));
                    if (!forwarded) continue;
                    block.Statements[i] = rewritten;
                    changed = true;
                }
            foreach (var block in function.Blocks)
                changed |= block.Statements.RemoveAll(s => s is Store { Value.Width: > 0 } store && model.Slot(store.Target) is { } slot
                    && slot < 0 && model.Unobserved(slot, store.Value.Width / 8)) > 0;
            if (!changed) break;
            any = true;
        }
        return any;
    }

    private static Expr? Forward(FrameModel model, Block block, int index, Load load)
    {
        if (load.Width % 8 != 0 || model.Slot(load.Address) is not { } slot) return null;
        var reach = model.Reach(block, index, slot, load.Width / 8);
        if (!reach.Complete) return null;
        var values = reach.Stores.Select(store => Bits(model, store, slot, load.Width)).Distinct().ToArray();
        return values is [{ } value] ? value : null;
    }

    private static Expr? Bits(FrameModel model, Store store, long slot, int width)
    {
        if (ExprMap.Walk(store.Value).Any(e => e is Load or Intrinsic or Flags or TestFlags or ConditionalFlags)) return null;
        return Fold.Extract(store.Value, checked((int)(slot - model.Slot(store.Target)!.Value) * 8), width);
    }
}
