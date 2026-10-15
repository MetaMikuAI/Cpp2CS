using Cpp2CS.Functions;
using Cpp2CS.Ir;

namespace Cpp2CS.Flow;

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
    /// 表项个数取自某个前驱块末尾对同一索引的无符号上界检查。任何一步不符合即放弃。
    /// </summary>
    public static ulong[]? Resolve(IMachine machine, Block block, Dictionary<ulong, Block> blockAt, Func<ulong, bool> inRange)
    {
        var state = new SymbolicState(machine.Convention);
        foreach (var stmt in block.Statements.Take(block.Statements.Count - 1)) state.Step(stmt);
        var jump = (IndirectJump)block.Statements[^1];
        var resolver = new EntryConstants(machine);
        // 表基址常在循环外算好放在被调用者保存的寄存器里：把能沿前驱确定为常量的入口值代入
        var target = Fold.Simplify(ExprMap.Map(state.Eval(jump.Target), e => e is Read r ? resolver.Resolve(r, block) : null));
        var loads = ExprMap.Walk(target).OfType<Load>().ToList();
        if (loads.Count != 1) return null;
        var load = loads[0];
        if (!Decompose(load.Address, out var tableBase, out var index, out var scale)) return null;
        var root = StripExtensions(index);
        if (root is not Read { Storage.Bank: Bank.Gpr } read) return null;

        foreach (var predecessor in block.Predecessors)
        {
            if (Bound(machine, predecessor, block, read) is not { } count) continue;
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

    /// <summary>前驱块以“index 超界则跳到别处”的分支结尾时，返回表项个数。</summary>
    private static int? Bound(IMachine machine, Block predecessor, Block block, Read index)
    {
        if (predecessor.Statements.LastOrDefault() is not Branch branch) return null;
        var state = new SymbolicState(machine.Convention);
        foreach (var stmt in predecessor.Statements.Take(predecessor.Statements.Count - 1)) state.Step(stmt);
        if (state.Eval(branch.Condition) is not Compare { Right: Const limit } compare) return null;
        var takenToBlock = branch.Target == block.Start;
        var fallToBlock = branch.Fallthrough == block.Start;
        if (takenToBlock == fallToBlock) return null;
        var atEnd = state.Eval(new Read(index.Storage, index.Storage.Width));
        if (Fold.Convert(ConvKind.Truncate, atEnd, compare.Left.Width) != compare.Left) return null;
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
/// </summary>
internal sealed class EntryConstants(IMachine machine)
{
    private const int MaxDepth = 64;
    /// <summary>只缓存确定的结论（常量或失败），依赖乐观环假设的结果不缓存。</summary>
    private readonly Dictionary<(Block, Storage), Const?> memo = new();
    private readonly HashSet<(Block, Storage)> visiting = [];

    public Expr? Resolve(Read read, Block block) =>
        read.Storage.Bank == Bank.Gpr && read.Storage != machine.Convention.StackPointer && Entry(block, read.Storage, 0, out _) is { } value
            ? Fold.Convert(ConvKind.Truncate, value, read.Width)
            : null;

    /// <param name="open">结果为 null 且只因所有前驱都在环上（尚无约束），而不是确定失败。</param>
    private Const? Entry(Block block, Storage storage, int depth, out bool open)
    {
        open = false;
        var key = (block, storage);
        if (memo.TryGetValue(key, out var cached)) return cached;
        if (visiting.Contains(key)) { open = true; return null; }
        if (depth > MaxDepth || block.Predecessors.Count == 0) return null;
        visiting.Add(key);
        Const? agreed = null;
        bool failed = false, anyOpen = false;
        foreach (var predecessor in block.Predecessors)
        {
            var state = new SymbolicState(machine.Convention);
            // 异常边：调用会破坏调用者保存的寄存器，Step(Call) 已把它们置为未知
            foreach (var stmt in predecessor.Statements) state.Step(stmt);
            var value = state.Eval(new Read(storage, storage.Width));
            Const? found = null;
            if (value is Const c) found = c;
            else if (value is Read { Storage.Bank: Bank.Gpr } r && r.Width == storage.Width)
            {
                found = Entry(predecessor, r.Storage, depth + 1, out var predecessorOpen);
                if (found is null && predecessorOpen) { anyOpen = true; continue; }
            }
            if (found is null || agreed is not null && agreed.Value != found.Value) { failed = true; break; }
            agreed = found;
        }
        visiting.Remove(key);
        if (failed)
        {
            // 加入环上的取值只会更难一致，所以失败是确定的
            memo[key] = null;
            return null;
        }
        if (agreed is null) { open = true; return null; }
        if (!anyOpen) memo[key] = agreed;
        return agreed;
    }
}
