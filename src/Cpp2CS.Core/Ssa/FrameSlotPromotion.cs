using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Ssa;

/// <summary>
/// 帧槽提升（mem2reg）：把不逃逸的标量栈槽改写成存储单元 <see cref="Storage.Slot"/> 的读写，
/// 随后由 <see cref="SsaBuilder"/> 只对栈槽再构建一次 SSA。只提升满足下列全部条件的槽：
/// 1. 槽在本帧内（相对入口 SP 的偏移为负）；正偏移是调用者的帧（栈传入的参数）。
/// 2. 每次访问都是对这个偏移的直接读或写（地址是 FrameAddress、它与常量的加减，或定义为这两者的变量），位宽相同且不超过 64。
/// 3. 至少读一次、写一次。只写不读的槽可能是出参或隐藏的栈参数（被调用者隐式读取，调用模型不登记这种读取），保持原样。
/// 4. 没有其他访问与它的字节区间重叠。
/// 5. 没有地址逃逸到它的下方或它本身：逃逸的地址（作为实参、被存储、进入 φ、参与其他运算）可能被用来访问它之上的整块区域，
///    例如按指针传出的结构体局部。调用签名给出长度时，只阻止提升与该区间重叠的槽。
/// 原生对照不观察栈帧内容，提升不改变可观察行为；被删去的只是帧内的写入。
/// </summary>
public static class FrameSlotPromotion
{
    private sealed record Access(long Offset, int Width, bool IsStore);

    /// <summary>改写可提升的槽，返回提升的个数（为 0 时函数不变）。</summary>
    public static int Run(MachineFunction function, Func<Call, int, int?>? argumentSize = null,
        IReadOnlyList<(long Offset, int Size)>? preserved = null)
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

        static bool Overlap(Access a, Access b) => a.Offset < b.Offset + b.Width / 8 && b.Offset < a.Offset + Math.Max(1, a.Width / 8);
        var promoted = new Dictionary<long, int>();
        foreach (var group in accesses.GroupBy(a => a.Offset))
        {
            var offset = group.Key;
            var widths = group.Select(a => a.Width).Distinct().ToArray();
            if (offset >= 0 || widths is not [var width and (8 or 16 or 32 or 64)]) continue;
            if (escapes.Any(e => offset + width / 8 > e.Offset && (e.Size is not { } size || offset < e.Offset + size))) continue;
            if (preserved?.Any(r => offset + width / 8 > r.Offset && offset < r.Offset + r.Size) == true) continue;
            if (!group.Any(a => a.IsStore) || !group.Any(a => !a.IsStore)) continue;
            var own = new Access(offset, width, false);
            if (accesses.Any(a => a.Offset != offset && Overlap(a, own))) continue;
            promoted[offset] = width;
        }
        if (promoted.Count == 0) return 0;

        Expr? Promote(Expr e) => e is Load load && Resolve(load.Address) is { } o && promoted.ContainsKey(o)
            ? new Read(Storage.Slot(checked((int)o)), load.Width) : null;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                if (statement is Store store && Resolve(store.Target) is { } o && promoted.ContainsKey(o))
                    block.Statements[i] = new Assign(store.Address, Storage.Slot(checked((int)o)), ExprMap.Map(store.Value, Promote));
                else if (ExprMap.Operands(statement).SelectMany(ExprMap.Walk).Any(e => e is Load l && Resolve(l.Address) is { } lo && promoted.ContainsKey(lo)))
                    block.Statements[i] = ExprMap.MapOperands(statement, e => ExprMap.Map(e, Promote));
            }
        return promoted.Count;
    }
}
