using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Ssa;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>
/// 帧槽提升（mem2reg）：把不逃逸的标量栈槽改写成存储单元 <see cref="Storage.Slot"/> 的读写，
/// 随后由 <see cref="SsaBuilder"/> 只对栈槽再构建一次 SSA。只提升满足下列全部条件的槽：
/// 1. 槽在本帧内（相对入口 SP 的偏移为负）；正偏移是调用者的帧（栈传入的参数）。
/// 2. 每次访问都是直接读或写（地址是 FrameAddress、它与常量的加减，或定义为这两者的变量），重叠范围合并后不超过 128 位。
/// 3. 至少读一次、写一次。只写不读的槽可能是出参或隐藏的栈参数（被调用者隐式读取，调用模型不登记这种读取），保持原样。
/// 4. 部分写入保留同一区域未覆盖的位；读写均由同一存储单元表示。
/// 5. 没有地址逃逸到它的下方或它本身：逃逸的地址（作为实参、被存储、进入 φ、参与其他运算）可能被用来访问它之上的整块区域，
///    例如按指针传出的结构体局部。调用签名给出长度时，只阻止提升与该区间重叠的槽。
/// 原生对照不观察栈帧内容，提升不改变可观察行为；被删去的只是帧内的写入。
/// </summary>
public static class FrameSlotPromotion
{
    private sealed record Access(long Offset, int Width, bool IsStore);

    /// <summary>调用前保存、调用后原位读回的独占帧槽；调用必须已证明不会访问调用者的栈。</summary>
    internal static bool ForwardCallSpills(MachineFunction function, Func<Call, bool> safeCall, Func<Call, bool>? explicitInputs = null)
    {
        var changed = false;
        var dominators = Dominators.Compute(function);
        foreach (var block in function.Blocks)
            foreach (var store in block.Statements.OfType<Store>().ToArray())
            {
                if (store is not { Target: FrameAddress { Offset: <= -16 } frame, Value: Use or Const } || store.Value.Width != 128) continue;
                var index = block.Statements.IndexOf(store);
                Load? Reload(Expr value) => value switch
                {
                    Load { Width: 32 or 64 or 128, Address: FrameAddress read } load when read == frame => load,
                    Ir.Convert { Kind: ConvKind.ZeroExtend } conversion => Reload(conversion.Operand),
                    _ => null,
                };
                var restores = function.Blocks.SelectMany(b => b.Statements.OfType<Define>().Select(d => (Block: b, Define: d)))
                    .Where(p => Reload(p.Define.Value) is not null).ToArray();
                if (restores is not [var restored]) continue;
                var restore = restored.Define;
                if (restored.Block == block ? block.Statements.IndexOf(restore) <= index
                    : !dominators.Dominates(block.Index, restored.Block.Index)) continue;
                bool Exposes(Expr e) => e switch
                {
                    // 只接受没有别名或部分访存的独占区域；其他帧地址只允许直接读写不相交的区间。
                    Load { Address: FrameAddress at } load => at.Offset < frame.Offset + 16 && frame.Offset < at.Offset + load.Width / 8,
                    FrameAddress at => at.Offset <= frame.Offset + 15,
                    _ => ExprMap.Children(e).Any(Exposes),
                };
                bool OtherAccess(Stmt statement)
                {
                    if (ReferenceEquals(statement, store) || ReferenceEquals(statement, restore)) return false;
                    if (statement is Store { Target: FrameAddress at } write)
                        return at.Offset < frame.Offset + 16 && frame.Offset < at.Offset + write.Value.Width / 8 || Exposes(write.Value);
                    // 已知签名的栈实参已展开在 Arguments 中；保存的 SP 仅记录调用位置。
                    if (statement is Call call && (safeCall(call) || explicitInputs?.Invoke(call) == true))
                        return Exposes(call.Target) || call.Arguments.Any(Exposes) || call.DelegateReceiver is { } receiver && Exposes(receiver);
                    return ExprMap.Operands(statement).Any(Exposes);
                }
                if (function.Blocks.SelectMany(b => b.Statements).Any(OtherAccess)) continue;
                var visited = new HashSet<Block>();
                bool SafePath(Block current, int begin)
                {
                    if (!visited.Add(current)) return false;
                    foreach (var statement in current.Statements.Skip(begin))
                    {
                        if (ReferenceEquals(statement, restore)) return true;
                        if (ReferenceEquals(statement, store) || statement is Call call && !safeCall(call)) return false;
                    }
                    return current.Successors.All(next => visited.Contains(next) && next != block || SafePath(next, 0));
                }
                if (!SafePath(block, index + 1)) continue;
                var loaded = Reload(restore.Value)!;
                restored.Block.Statements[restored.Block.Statements.IndexOf(restore)] = restore with
                { Value = Fold.Simplify(ExprMap.Map(restore.Value, e => ReferenceEquals(e, loaded) ? Fold.Extract(store.Value, 0, loaded.Width) : null)) };
                block.Statements.Remove(store);
                changed = true;
            }
        return changed;
    }

    /// <summary>改写可提升的槽，返回提升的个数（为 0 时函数不变）。</summary>
    public static int Run(MachineFunction function, Func<Call, int, int?>? argumentSize = null,
        IReadOnlyList<(long Offset, int Size)>? preserved = null, bool overlapping = false)
        => Transform(function, argumentSize, preserved, overlapping, false);

    /// <summary>转发独占标量槽中唯一且支配所有读取的保存值，保留原始写入供调用 ABI 使用。</summary>
    internal static int ForwardSingleStores(MachineFunction function) => Transform(function, null, null, false, true);

    private static int Transform(MachineFunction function, Func<Call, int, int?>? argumentSize,
        IReadOnlyList<(long Offset, int Size)>? preserved, bool overlapping, bool forwardOnly)
    {
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var aliases = new Dictionary<Variable, long>();
        long? Resolve(Expr e) => e switch
        {
            FrameAddress f => f.Offset,
            Use { Width: 64 } u when aliases.TryGetValue(u.Variable, out var o) => o,
            Binary { Op: BinOp.Add, Right: Const c } b when Resolve(b.Left) is { } o => o + c.Signed,
            Binary { Op: BinOp.Add, Left: Const c } b when Resolve(b.Right) is { } o => o + c.Signed,
            Binary { Op: BinOp.Sub, Right: Const c } b when Resolve(b.Left) is { } o => o - c.Signed,
            _ => null,
        };
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var define in statements.OfType<Define>())
                if (define.Target.Width == 64 && !aliases.ContainsKey(define.Target) && Resolve(define.Value) is { } offset) { aliases[define.Target] = offset; changed = true; }
        }

        var accesses = new List<Access>();
        var escapes = new List<(long Offset, int? Size)>();
        void Visit(Expr e, int? size = null)
        {
            if (e is Load load && Resolve(load.Address) is { } loaded)
            {
                accesses.Add(new(loaded, load.Width, false));
                return;
            }
            if (Resolve(e) is { } escaped) { escapes.Add((escaped, size)); return; }
            foreach (var child in ExprMap.Children(e)) Visit(child);
        }
        foreach (var statement in statements)
            switch (statement)
            {
                // 别名的定义本身不是逃逸；它的每个使用各自分类。
                case Define define when aliases.ContainsKey(define.Target): break;
                case Store store when Resolve(store.Target) is { } stored:
                    accesses.Add(new(stored, store.Value.Width, true));
                    Visit(store.Value);
                    break;
                case Phi phi:
                    foreach (var source in phi.Sources)
                        if (aliases.TryGetValue(source, out var merged)) escapes.Add((merged, null));
                    break;
                case Call call:
                    Visit(call.Target);
                    if (call.DelegateReceiver is { } receiver) Visit(receiver);
                    for (var i = 0; i < call.Arguments.Length; i++)
                        Visit(call.Arguments[i], Resolve(call.Arguments[i]) is not null ? argumentSize?.Invoke(call, i) : null);
                    break;
                default:
                    foreach (var operand in ExprMap.Operands(statement)) Visit(operand);
                    break;
            }
        if (accesses.Count == 0) return 0;

        var promoted = new Dictionary<long, int>();
        var splitZeros = new HashSet<Store>(ReferenceEqualityComparer.Instance);
        var zeroVectors = statements.OfType<Define>().Where(d => d.Value is Const { Value: 0, Width: 128 }).Select(d => d.Target).ToHashSet();
        var groups = new List<List<Access>>();
        foreach (var access in accesses.OrderBy(a => a.Offset))
        {
            if (groups.Count == 0 || access.Offset >= groups[^1].Max(a => a.Offset + Math.Max(1, a.Width / 8)))
                groups.Add([]);
            groups[^1].Add(access);
        }
        foreach (var group in groups)
        {
            // 混合宽度须等托管签名划出结构体范围，避免拆散包含引用的 ABI 分量。
            if (!overlapping && (group.Select(a => a.Offset).Distinct().Count() != 1 || group.Select(a => a.Width).Distinct().Count() != 1)) continue;
            var offset = group[0].Offset;
            var width = checked((int)(group.Max(a => a.Offset + a.Width / 8) - offset) * 8);
            if (offset >= 0 || width is not (8 or 16 or 32 or 64 or 128) || group.Any(a => a.Width is not (8 or 16 or 32 or 64 or 128)) || offset + width / 8 > 0) continue;
            var mixed = group.Select(a => a.Offset).Distinct().Count() != 1 || group.Select(a => a.Width).Distinct().Count() != 1;
            if (escapes.Any(e => offset + width / 8 > e.Offset && (e.Size is not { } size || offset < e.Offset + size))) continue;
            if (preserved?.Any(r => offset + width / 8 > r.Offset && offset < r.Offset + r.Size) == true) continue;
            // 向量清零可覆盖相邻独立局部。完整区域已通过逃逸/聚合检查，再拆成各自的存储单元。
            if (overlapping && mixed && width == 128 && group.Any(a => !a.IsStore && a.Width == 64)
                && group.All(a => a.IsStore && a.Width == 128 || a.Width <= 64 && (a.Offset - offset) % 8 + a.Width / 8 <= 8))
            {
                var wide = statements.OfType<Store>().Where(s => s.Value.Width == 128 && Resolve(s.Target) == offset).ToArray();
                if (wide.Length > 0 && wide.All(s => s.Value is Const { Value: 0 } || s.Value is Use u && zeroVectors.Contains(u.Variable)))
                {
                    splitZeros.UnionWith(wide);
                    continue;
                }
            }
            // 同起点暂存只观察低位，且每次写入都覆盖这些位：按读取宽度提升，保留完整区域的逃逸检查。
            if (overlapping && mixed && group.All(a => a.Offset == offset)
                && group.Where(a => !a.IsStore).Select(a => a.Width).Distinct().ToArray() is [var observed and (32 or 64)]
                && group.Where(a => a.IsStore).All(a => a.Width >= observed)) width = observed;
            // 向量聚合及部分浮点写入仍交给有类型的字段路径，避免把引用或浮点局部变成整数位段。
            if (mixed && (width == 128 || statements.OfType<Store>().Any(s => s.Value is Use { Variable.Storage.Bank: Bank.Vec }
                && s.Value.Width < width && Resolve(s.Target) is { } at && at >= offset && at < offset + width / 8))) continue;
            if (!group.Any(a => a.IsStore) || !group.Any(a => !a.IsStore)) continue;
            promoted[offset] = width;
        }
        if (splitZeros.Count > 0)
        {
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    if (block.Statements[i] is Store store && splitZeros.Contains(store))
                    {
                        var offset = Resolve(store.Target)!.Value;
                        block.Statements[i] = new Store(store.Address, new FrameAddress(offset), Expr.C(0, 64));
                        block.Statements.Insert(++i, new Store(store.Address, new FrameAddress(offset + 8), Expr.C(0, 64)));
                    }
            return Run(function, argumentSize, preserved, overlapping);
        }
        if (promoted.Count == 0) return 0;

        if (forwardOnly)
        {
            var positions = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i)))
                .ToDictionary(p => p.Statement, (IEqualityComparer<Stmt>)ReferenceEqualityComparer.Instance);
            var dominators = Dominators.Compute(function);
            var values = new Dictionary<long, Expr>();
            foreach (var (offset, width) in promoted)
            {
                if (width > 64 || statements.OfType<Store>().Where(s => Resolve(s.Target) == offset).ToArray()
                    is not [var store] || store.Value is not (Use or Const)) continue;
                var written = positions[store];
                var reads = positions.Values.Where(p => ExprMap.Operands(p.Statement).SelectMany(ExprMap.Walk)
                    .Any(e => e is Load l && Resolve(l.Address) == offset));
                if (reads.Any(p => p.Block == written.Block ? p.Index <= written.Index
                    : !dominators.Dominates(written.Block.Index, p.Block.Index))) continue;
                values[offset] = store.Value;
            }
            Expr? Forward(Expr e) => e is Load l && Resolve(l.Address) is { } offset && values.TryGetValue(offset, out var value) ? value : null;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Forward));
            return values.Count;
        }

        var slots = accesses.Where(a => promoted.Any(p => a.Offset >= p.Key && a.Offset + a.Width / 8 <= p.Key + p.Value / 8))
            .Select(a => a.Offset).Distinct().ToDictionary(o => o, o => promoted.Single(p => o >= p.Key && o < p.Key + p.Value / 8).Key);
        Storage Slot(long origin) => Storage.Slot(checked((int)origin), Math.Max(64, promoted[origin]));
        Expr? Promote(Expr e) => e is Load load && Resolve(load.Address) is { } o && slots.TryGetValue(o, out var origin)
            ? o == origin ? new Read(Slot(origin), load.Width)
                : Fold.Extract(new Read(Slot(origin), Slot(origin).Width), checked((int)(o - origin) * 8), load.Width) : null;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                if (statement is Store store && Resolve(store.Target) is { } o && slots.TryGetValue(o, out var origin))
                {
                    var slot = Slot(origin);
                    var value = ExprMap.Map(store.Value, Promote);
                    if (o == origin && value.Width > promoted[origin]) value = Fold.Extract(value, 0, promoted[origin]);
                    block.Statements[i] = new Assign(store.Address, slot, o == origin && value.Width == promoted[origin]
                        ? value : Fold.Insert(new Read(slot, slot.Width), value, checked((int)(o - origin) * 8)));
                }
                else if (ExprMap.Operands(statement).SelectMany(ExprMap.Walk).Any(e => e is Load l && Resolve(l.Address) is { } lo && slots.ContainsKey(lo)))
                    block.Statements[i] = ExprMap.MapOperands(statement, e => ExprMap.Map(e, Promote));
            }
        return promoted.Count;
    }
}
