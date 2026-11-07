using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Flow;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>基本块内的符号执行：寄存器取值表示为块入口值的表达式。只用于局部模式（跳转表、PLT 桩）。</summary>
internal sealed class SymbolicState(CallingConvention convention)
{
    private readonly Dictionary<Storage, Expr> values = new();

    public Expr Eval(Expr expr) => Fold.Simplify(ExprMap.Map(expr, e => e is Read read && values.TryGetValue(read.Storage, out var value)
        ? Fold.Convert(ConvKind.Truncate, value, read.Width)
        : null));

    public void Step(Stmt stmt)
    {
        switch (stmt)
        {
            case Assign assign:
                var value = Eval(assign.Value);
                if (assign.Target.Bank != Bank.Flags && value.Width < assign.Target.Width) value = Fold.Convert(ConvKind.ZeroExtend, value, assign.Target.Width);
                values[assign.Target] = value;
                break;
            case Call:
                foreach (var storage in convention.Clobbered) values[storage] = new Unknown("clobbered", storage.Width);
                break;
            case Opaque:
                values.Clear();
                break;
        }
    }
}

internal static class JumpTables
{
    private const int MaxEntries = 4096;

    /// <summary>
    /// 解析以寄存器跳转结尾的块：目标形如 base + ext(table[index]) &lt;&lt; k（或 table[index] 本身），
    /// 表项个数取自某个前驱块末尾对同一索引的无符号上界检查，或由调用方给出（<paramref name="knownCount"/>，已在别处证明）。任何一步不符合即放弃。
    /// </summary>
    public static ulong[]? Resolve(IMachine machine, Block block, Dictionary<ulong, Block> blockAt, Func<ulong, bool> inRange, int? knownCount = null)
    {
        var state = new SymbolicState(machine.Convention);
        foreach (var stmt in block.Statements.Take(block.Statements.Count - 1)) state.Step(stmt);
        var jump = (IndirectJump)block.Statements[^1];
        var resolver = new EntryConstants(machine);
        // 表基址常在循环外算好放在被调用者保存的寄存器里：把能沿前驱确定为常量的入口值代入
        var target = Fold.Simplify(ExprMap.Map(state.Eval(jump.Target), e => e is Read r ? resolver.Resolve(r, block) : null));
        // 查表是最外层的读取；下标本身也可以来自读取（栈槽里的副本），嵌在查表地址里。
        var loads = ExprMap.Walk(target).OfType<Load>().ToList();
        var outer = loads.Where(l => !loads.Any(o => !ReferenceEquals(o, l) && ExprMap.Walk(o.Address).Any(e => ReferenceEquals(e, l)))).ToList();
        if (outer.Count != 1) return null;
        var load = outer[0];
        if (!Decompose(load.Address, out var tableBase, out var index, out var scale)) return null;
        var root = StripExtensions(index);
        // 上界由前驱的检查给出时，下标要是能和检查对上的寄存器；个数已在别处证明时不需要。
        if (knownCount is null && root is not Read { Storage.Bank: Bank.Gpr }
            && !(root is Binary { Op: BinOp.And, Left: var masked, Right: Const { Value: <= uint.MaxValue } } && StripExtensions(masked) is Read { Storage.Bank: Bank.Gpr })) return null;

        IEnumerable<int?> counts = knownCount is { } given ? [given] : block.Predecessors.Select(predecessor => Bound(machine.Convention, predecessor, block, root));
        foreach (var candidate in counts)
        {
            if (candidate is not { } count) continue;
            if (count <= 0 || count > MaxEntries) return null;
            var targets = new ulong[count];
            for (var i = 0; i < count; i++)
            {
                var address = tableBase + (ulong)i * scale;
                Expr entry;
                if (load.Width == 64)
                {
                    if (machine.Image.ReadPointer(address) is not { } pointer) return null;
                    entry = Expr.C(pointer, 64);
                }
                else
                {
                    var bytes = machine.Image.ReadUpTo(address, load.Width / 8);
                    if (bytes.Length < load.Width / 8) return null;
                    ulong raw = 0;
                    for (var b = bytes.Length - 1; b >= 0; b--) raw = (raw << 8) | bytes[b];
                    entry = Expr.C(raw, load.Width);
                }
                var resolved = Fold.Simplify(ExprMap.Map(target, e => ReferenceEquals(e, load) ? entry : null));
                if (resolved is not Const c || !inRange(c.Value)) return null;
                targets[i] = c.Value;
            }
            return targets;
        }
        return null;
    }

    private static bool Decompose(Expr address, out ulong tableBase, out Expr index, out ulong scale)
    {
        tableBase = 0;
        index = address;
        scale = 1;
        if (address is not Binary { Op: BinOp.Add, Right: Const baseConst } add) return false;
        tableBase = baseConst.Value;
        switch (add.Left)
        {
            case Binary { Op: BinOp.Shl, Right: Const shift } shl:
                index = shl.Left;
                scale = 1UL << (int)shift.Value;
                break;
            case Binary { Op: BinOp.Mul, Right: Const factor } mul:
                index = mul.Left;
                scale = factor.Value;
                break;
            default:
                index = add.Left;
                break;
        }
        return true;
    }

    private static Expr StripExtensions(Expr expr)
    {
        while (expr is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } c) expr = c.Operand;
        return expr;
    }

    /// <summary>值的低 width 位。按位与和扩展移到截断之内，使宽度不同的同一计算（and x8, x0, #mask 与 and w8, w0, #mask）形式一致。</summary>
    private static Expr LowBits(Expr value, int width) => value switch
    {
        _ when value.Width == width => value,
        Binary { Op: BinOp.And, Left: var left, Right: Const mask } when value.Width > width
            => Fold.Simplify(new Binary(BinOp.And, LowBits(left, width), Expr.C(mask.Value & (width >= 64 ? ulong.MaxValue : (1UL << width) - 1), width), width)),
        Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: var operand } when operand.Width >= width => LowBits(operand, width),
        _ => Fold.Convert(ConvKind.Truncate, value, width),
    };

    /// <summary>前驱块以“index 超界则跳到别处”的分支结尾时，返回表项个数。</summary>
    internal static int? Bound(CallingConvention convention, Block predecessor, Block block, Expr index)
    {
        if (predecessor.Statements.LastOrDefault() is not Branch branch) return null;
        var state = new SymbolicState(convention);
        foreach (var stmt in predecessor.Statements.Take(predecessor.Statements.Count - 1)) state.Step(stmt);
        if (state.Eval(branch.Condition) is not Compare { Right: Const limit } compare) return null;
        var takenToBlock = branch.Target == block.Start;
        var fallToBlock = branch.Fallthrough == block.Start;
        if (takenToBlock == fallToBlock) return null;
        var atEnd = state.Eval(index);
        if (LowBits(atEnd, compare.Left.Width) != compare.Left) return null;
        var n = limit.Value;
        ulong? count = (compare.Cond, takenToBlock) switch
        {
            (Cond.Ult, true) or (Cond.Uge, false) => n,
            (Cond.Ule, true) or (Cond.Ugt, false) => n + 1,
            _ => null,
        };
        return count is { } value && value <= MaxEntries ? (int)value : null;
    }
}

/// <summary>
/// 寄存器在块入口的常量值：所有前驱末尾的取值（递归到前驱的入口）都是同一个常量时成立。
/// 只在环上原样传递的前驱不提供约束（乐观处理，与稀疏条件常量传播一致）。
/// 表基址可以在很远的前驱里算好（大方法里隔着很多块），这里按工作表逐块回溯，不受路径长度限制。
/// </summary>
internal sealed class EntryConstants(IMachine machine)
{
    private const int MaxNodes = 1 << 16;
    private readonly Dictionary<(Block, Storage), Const?> memo = new();
    private readonly Dictionary<Block, SymbolicState> ends = new();

    public Expr? Resolve(Read read, Block block) =>
        read.Storage.Bank == Bank.Gpr && read.Storage != machine.Convention.StackPointer && Entry(block, read.Storage) is { } value
            ? Fold.Convert(ConvKind.Truncate, value, read.Width)
            : null;

    private Const? Entry(Block block, Storage storage)
    {
        if (memo.TryGetValue((block, storage), out var known)) return known;
        return memo[(block, storage)] = Solve(block, storage);
    }

    private Const? Solve(Block start, Storage storage)
    {
        var visited = new HashSet<(Block, Storage)> { (start, storage) };
        var pending = new Stack<(Block Block, Storage Storage)>();
        pending.Push((start, storage));
        Const? agreed = null;
        while (pending.TryPop(out var node))
        {
            if (node.Block.Predecessors.Count == 0 || visited.Count > MaxNodes) return null;
            foreach (var predecessor in node.Block.Predecessors)
            {
                // 异常边：调用会破坏调用者保存的寄存器，Step(Call) 已把它们置为未知
                switch (End(predecessor).Eval(new Read(node.Storage, node.Storage.Width)))
                {
                    case Const c when agreed is null || agreed.Value == c.Value:
                        agreed = c;
                        break;
                    case Read { Storage.Bank: Bank.Gpr } r when r.Width == node.Storage.Width:
                        if (visited.Add((predecessor, r.Storage))) pending.Push((predecessor, r.Storage));
                        break;
                    default:
                        return null;
                }
            }
        }
        return agreed;
    }

    private SymbolicState End(Block block)
    {
        if (ends.TryGetValue(block, out var known)) return known;
        var state = new SymbolicState(machine.Convention);
        foreach (var statement in block.Statements) state.Step(statement);
        return ends[block] = state;
    }
}
