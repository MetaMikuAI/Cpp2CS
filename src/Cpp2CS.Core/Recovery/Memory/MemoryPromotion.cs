using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Recovery.Calls;

namespace Cpp2CS.Recovery.Memory;

/// <summary>局部内存的一个单元：重叠访问的并集。Escape 不为 null 时地址流向了无法确定访问范围的用途，单元不提升。</summary>
public sealed record Cell(int Id, LocalSpace Space, long Start, int Size, string? Escape)
{
    public bool Promoted => Escape is null;
    public long End => Start + Size;
    public Storage Storage => Storage.Local(Id, Size * 8);
    public override string ToString() => $"cell{Id} {Space}[{Start:x},{End:x}){(Escape is null ? "" : " 逃逸：" + Escape)}";
}

/// <summary>局部内存的划分。</summary>
public sealed class MemoryLayout(IReadOnlyList<Cell> cells)
{
    public IReadOnlyList<Cell> Cells { get; } = cells;
    public Cell? Of(Storage storage) => storage.Bank == Bank.Local ? Cells[storage.Index] : null;
    public Cell? Find(LocalSpace space, long offset, int size) =>
        Cells.FirstOrDefault(c => c.Space == space && c.Start <= offset && offset + Math.Max(size, 1) <= c.End);
}

/// <summary>
/// 局部内存的提升：收集栈帧、结果缓冲区和实参副本上的全部访问——直接读写、按机器签名经指针实参的调用效果、
/// 栈传递的实参——把重叠的访问区间合并为单元。地址流向其他用途（存入内存、进入 φ、未知调用、动态下标）的单元保留为内存；
/// 其余单元的读写改为单元的部分读写，调用按效果读取或写出单元，然后对单元构建 SSA。
/// 栈槽复用时完整写入开始新的版本；溢出读回经 SSA 得到原值。
/// </summary>
internal sealed class MemoryPromotion
{
    private sealed record Access(LocalSpace Space, long Offset, int Size, string? Escape);

    /// <summary>调用经指针的一次效果：Argument 为指针在 Arguments 中的位置（栈实参为 -1）。</summary>
    private sealed record Effect(int Argument, int Value, int ValueWidth, int ValueBit, LocalSpace Space, long Offset, int Size, MemoryAccess Access);

    private readonly MachineFunction function;
    private readonly MachineSignature signature;
    private readonly Func<Call, CallShape> shapes;
    private readonly ManagedAbi abi;
    private readonly Dictionary<Variable, Expr> definitions = [];
    private readonly Dictionary<Storage, LocalSpace> pointers = [];
    private readonly List<Access> accesses = [];

    private MemoryPromotion(MachineFunction function, MachineSignature signature, Func<Call, CallShape> shapes, ManagedAbi abi)
    {
        this.function = function;
        this.signature = signature;
        this.shapes = shapes;
        this.abi = abi;
        foreach (var value in signature.Arguments.Where(a => a.Transfer == Transfer.Copy && a.Pieces[0].Register.Bank == Bank.Gpr))
            pointers[value.Pieces[0].Register] = LocalSpace.Copy(value.Index);
        if (signature.Return is { Transfer: Transfer.ResultBuffer } result && result.Pieces[0].Register.Bank == Bank.Gpr)
            pointers[result.Pieces[0].Register] = LocalSpace.Result;
    }

    public static RecoveryResult<MemoryLayout> Run(MachineFunction function, MachineSignature signature, Func<Call, CallShape> shapes,
        ManagedAbi abi, ICallModel calls, Storage stackPointer)
    {
        var promotion = new MemoryPromotion(function, signature, shapes, abi);
        var layout = promotion.Partition();
        if (layout.Cells.Count == 0) return layout;
        if (signature.Return is { Transfer: Transfer.ResultBuffer } && layout.Cells.Any(c => c.Space == LocalSpace.Result && !c.Promoted))
            return RecoveryDiagnostics.Fail(function.Entry, "内存 结果缓冲区的地址逃逸", rule: "Memory");
        promotion.Rewrite(layout);
        var dominators = Dominators.Compute(function);
        SsaBuilder.Build(function, dominators, s => s.Bank == Bank.Local, calls, stackPointer);
        if (SsaCheck.Verify(function, dominators) is [var error, ..])
            return RecoveryDiagnostics.Fail(function.Entry, $"内存 单元 SSA：{error}", rule: "Memory");
        Propagate.Run(function, dominators);
        return layout;
    }

    // ---- 地址 ----

    /// <summary>局部地址：帧地址、副本或结果缓冲区指针的入口值，加常量。</summary>
    private (LocalSpace Space, long Offset)? Resolve(Expr expression, int depth = 0)
    {
        if (depth > 16) return null;
        return expression switch
        {
            FrameAddress f => (LocalSpace.Frame, f.Offset),
            Entry { Storage: var s } when pointers.TryGetValue(s, out var space) => (space, 0),
            Use { Variable: { Version: 0 } v } when pointers.TryGetValue(v.Storage, out var space) => (space, 0),
            Use { Variable: var v, Width: 64 } when definitions.TryGetValue(v, out var value) => Resolve(value, depth + 1),
            Binary { Op: BinOp.Add, Right: Const c } b when Resolve(b.Left, depth + 1) is var (space, offset) => (space, offset + unchecked((long)c.Value)),
            Binary { Op: BinOp.Sub, Right: Const c } b when Resolve(b.Left, depth + 1) is var (space, offset) => (space, offset - unchecked((long)c.Value)),
            _ => null,
        };
    }

    // ---- 收集 ----

    private MemoryLayout Partition()
    {
        foreach (var block in function.Blocks)
            foreach (var statement in block.Statements)
                if (statement is Define define) definitions[define.Target] = define.Value;
        foreach (var block in function.Blocks)
            foreach (var statement in block.Statements)
                Collect(statement);
        var cells = new List<Cell>();
        foreach (var group in accesses.GroupBy(a => a.Space))
        {
            var ordered = group.OrderBy(a => a.Offset).ToList();
            var start = ordered[0].Offset;
            var end = start + Math.Max(1, ordered[0].Size);
            string? escape = ordered[0].Escape;
            foreach (var access in ordered.Skip(1))
            {
                if (access.Offset < end)
                {
                    end = Math.Max(end, access.Offset + Math.Max(1, access.Size));
                    escape ??= access.Escape;
                    continue;
                }
                cells.Add(Make(cells.Count, group.Key, start, end, escape));
                (start, end, escape) = (access.Offset, access.Offset + Math.Max(1, access.Size), access.Escape);
            }
            cells.Add(Make(cells.Count, group.Key, start, end, escape));
        }
        return new MemoryLayout(cells);
    }

    private static Cell Make(int id, LocalSpace space, long start, long end, string? escape) =>
        new(id, space, start, checked((int)(end - start)), escape ?? (end - start > 4096 ? "单元超过 4096 字节" : null));

    private void Add(LocalSpace space, long offset, int size) => accesses.Add(new(space, offset, size, null));
    private void Escape(LocalSpace space, long offset, string reason) => accesses.Add(new(space, offset, 1, reason));

    private void Collect(Stmt statement)
    {
        switch (statement)
        {
            case Define define:
                if (Resolve(define.Value) is null) Walk(define.Value, "参与运算");
                break;
            case Phi phi:
                foreach (var source in phi.Sources)
                    if (source is not null && Resolve(new Use(source, 64)) is var (space, offset)) Escape(space, offset, "进入 φ");
                break;
            case Store store:
                if (Resolve(store.Target) is var (targetSpace, targetOffset)) Add(targetSpace, targetOffset, store.Value.Width / 8);
                else Walk(store.Target, "地址运算");
                Walk(store.Value, "存入内存");
                break;
            case Call { Op.Kind: OpKind.WriteBarrier or OpKind.MemoryBarrier }:
                // 写屏障只通知 GC，对应的写入是紧邻其前的 Store。
                break;
            case Call call:
                {
                    Walk(call.Target, "调用目标");
                    var effects = Effects(call);
                    foreach (var effect in effects)
                        if (effect.Size > 0) Add(effect.Space, effect.Offset, effect.Size);
                        else Escape(effect.Space, effect.Offset, "调用访问范围未知");
                    var covered = effects.Select(e => e.Argument).ToHashSet();
                    for (var i = 0; i < call.Arguments.Length; i++)
                        if (!covered.Contains(i)) Walk(call.Arguments[i], shapes(call) is { Signature: null, IsRuntime: false } ? "未知调用的实参" : "调用实参");
                    if (call.DelegateReceiver is { } receiver) Walk(receiver, "委托接收者");
                    break;
                }
            default:
                foreach (var operand in ExprMap.Operands(statement)) Walk(operand, "语句操作数");
                break;
        }
    }

    /// <summary>表达式中的读取是访问；其余位置出现的局部地址是逃逸。</summary>
    private void Walk(Expr expression, string reason)
    {
        if (expression is Load load)
        {
            if (Resolve(load.Address) is var (space, offset)) Add(space, offset, load.Width / 8);
            else Walk(load.Address, "地址运算");
            return;
        }
        if (expression is not Const && Resolve(expression) is var (local, at))
        {
            Escape(local, at, reason);
            return;
        }
        foreach (var child in ExprMap.Children(expression)) Walk(child, reason);
    }

    /// <summary>调用经指针实参与栈实参访问的局部内存。</summary>
    private List<Effect> Effects(Call call)
    {
        var effects = new List<Effect>();
        if (call.Op is { } op && !shapes(call).IsDispatch)
        {
            foreach (var effect in Runtime.RuntimeOps.Of(op.Kind)?.Effects?.Invoke(call, abi) ?? [])
                if (effect.Argument < call.Arguments.Length && Resolve(call.Arguments[effect.Argument]) is var (space, offset))
                    effects.Add(new(effect.Argument, effect.Value, effect.Size * 8, 0, space, offset, effect.Size, effect.Access));
            return effects;
        }
        if (shapes(call).Signature is not { } callee) return effects;
        foreach (var value in callee.Indirections)
        {
            var pointer = value.Pieces[0].Register;
            var position = Array.IndexOf(call.Sources, pointer);
            if (position < 0 || Resolve(call.Arguments[position]) is not var (space, offset)) continue;
            effects.Add(new(position, value.Index, value.Size * 8, 0, space, offset, value.Size, value.Access));
        }
        if (call.StackPointer is { } sp && Resolve(sp) is (LocalSpace { Kind: LocalKind.Frame }, var spOffset))
            foreach (var value in callee.Arguments.Where(a => a.Transfer == Transfer.Value))
                foreach (var piece in value.Pieces.Where(p => p.Register.Bank == Bank.Stack))
                    effects.Add(new(-1, value.Index, MethodEnvironment.ValueWidth(value), piece.Offset * 8, LocalSpace.Frame,
                        spOffset + piece.Register.Index, piece.Width / 8, MemoryAccess.Read));
        return effects;
    }

    // ---- 改写 ----

    private void Rewrite(MemoryLayout layout)
    {
        Cell? Promoted(LocalSpace space, long offset, int size) => layout.Find(space, offset, size) is { Promoted: true } cell ? cell : null;
        Expr Loads(Expr expression) => ExprMap.Map(expression, e =>
        {
            if (e is not Load load || Resolve(load.Address) is not var (space, offset) || Promoted(space, offset, load.Width / 8) is not { } cell) return null;
            var whole = new Read(cell.Storage, cell.Size * 8);
            return offset == cell.Start && load.Width == cell.Size * 8 ? whole : new Extract(whole, (int)(offset - cell.Start) * 8, load.Width);
        });
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                if (statement is Store store && Resolve(store.Target) is var (space, offset) && Promoted(space, offset, store.Value.Width / 8) is { } cell)
                {
                    var value = Loads(store.Value);
                    var whole = new Read(cell.Storage, cell.Size * 8);
                    Expr content = offset == cell.Start && value.Width == cell.Size * 8 ? value : new Insert(whole, value, (int)(offset - cell.Start) * 8);
                    block.Statements[i] = new Assign(store.Address, cell.Storage, content);
                    continue;
                }
                statement = ExprMap.MapOperands(statement, Loads);
                if (statement is Call call) statement = WithEffects(call, Effects(call), layout);
                if (statement is Return ret && signature.Return is { Transfer: Transfer.ResultBuffer })
                    statement = ret with
                    {
                        Pieces = layout.Cells.Where(c => c.Space == LocalSpace.Result).OrderBy(c => c.Start)
                            .Select(c => new ReturnPiece((int)c.Start, new Read(c.Storage, c.Size * 8))).ToArray(),
                    };
                block.Statements[i] = statement;
            }
    }

    private static Call WithEffects(Call call, List<Effect> effects, MemoryLayout layout)
    {
        var arguments = call.Arguments.ToList();
        var sources = call.Sources.ToList();
        var results = call.Results.ToList();
        var defines = call.Defines.Length == call.Results.Length ? call.Defines.ToList() : Enumerable.Repeat<Variable>(null!, call.Results.Length).ToList();
        var memory = new List<CellAccess>();
        foreach (var effect in effects)
        {
            if (effect.Size <= 0) continue;
            foreach (var cell in layout.Cells.Where(c => c.Promoted && c.Space == effect.Space && c.Start < effect.Offset + effect.Size && effect.Offset < c.End))
            {
                var from = Math.Max(cell.Start, effect.Offset);
                var to = Math.Min(cell.End, effect.Offset + effect.Size);
                var access = new CellAccess(cell.Storage, effect.Value, effect.ValueWidth, effect.ValueBit + (int)(from - effect.Offset) * 8,
                    (int)(from - cell.Start) * 8, (int)(to - from) * 8, false);
                var whole = from == cell.Start && to == cell.End;
                if ((effect.Access & MemoryAccess.Read) != 0 || !whole)
                {
                    if (!sources.Contains(cell.Storage)) { sources.Add(cell.Storage); arguments.Add(new Read(cell.Storage, cell.Size * 8)); }
                    if ((effect.Access & MemoryAccess.Read) != 0) memory.Add(access);
                }
                if ((effect.Access & MemoryAccess.Write) != 0)
                {
                    if (!results.Contains(cell.Storage)) { results.Add(cell.Storage); defines.Add(null!); }
                    memory.Add(access with { Write = true });
                }
            }
        }
        if (memory.Count == 0) return call;
        return call with { Arguments = arguments.ToArray(), Sources = sources.ToArray(), Results = results.ToArray(), Defines = defines.ToArray(), Memory = memory.ToArray() };
    }
}
