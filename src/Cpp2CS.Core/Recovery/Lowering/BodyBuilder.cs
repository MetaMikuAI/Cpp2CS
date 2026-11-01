using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>
/// 机械下降：按块把机器语句的效果写成托管语句。值从符号值按期望类型得到视图——数据搬运不产生语句，
/// 运算成为 IL 运算，读取按位置成为字段、元素或长度；读取只在被所在语句之外使用时落成局部；
/// 调用按机器签名重组 IL 实参，经指针的 ref 实参与结果缓冲区成为局部；φ 成为局部并在入边上并行赋值。
/// 表达不了的值与语句记为洞，方法体作为部分体保留。
/// </summary>
internal sealed class BodyBuilder
{
    private readonly MethodAnalysis analysis;
    private readonly TypeOracle oracle;
    private readonly ManagedTypes types;
    private readonly ValueModel values;
    private readonly Dictionary<Sym, LocalValue> locals = [];
    private readonly HashSet<ReadSym> materialized = [];
    private readonly HashSet<PhiSym> phis = [];
    private readonly List<RecoveryHole> holes = [];
    private readonly Dictionary<ResultSym, Call> constructions = [];
    private readonly HashSet<Sym> absorbedChecks = [];
    private int nextLocal;

    private BodyBuilder(MethodAnalysis analysis, TypeOracle oracle)
    {
        this.analysis = analysis;
        this.oracle = oracle;
        types = oracle.Types;
        values = analysis.Values;
    }

    public static MethodRecoveryResult Build(MethodAnalysis analysis, TypeOracle oracle) => new BodyBuilder(analysis, oracle).Run();

    private MethodRecoveryResult Run()
    {
        var function = analysis.Function;
        if (function.Blocks.Any(b => b.IsLandingPad))
            return new(analysis.Method, analysis.Entry, null, [new(analysis.Entry, "异常 区域尚未接入")]);
        // 读取只在被所在语句之外的 IL 值用到时落成局部：先空跑一遍记录用途，再正式下降。
        demand = [];
        LowerBlocks();
        var users = demand;
        demand = null;
        foreach (var (read, set) in users)
            if (set.Any(user => !ReferenceEquals(user, read.Site))) materialized.Add(read);
        locals.Clear(); phis.Clear(); holes.Clear(); constructions.Clear(); absorbedChecks.Clear(); nextLocal = 0;
        return LowerBlocks();
    }

    private MethodRecoveryResult LowerBlocks()
    {
        var function = analysis.Function;
        var lowered = new List<(Block Block, List<ManagedStatement> Statements, Terminator? Exit)>();
        foreach (var block in function.Blocks)
        {
            var output = new List<ManagedStatement>();
            Terminator? exit = null;
            for (var i = 0; i < block.Statements.Count && exit is null; i++)
            {
                current = block.Statements[i];
                exit = Lower(block, i, output);
            }
            if (exit is null && output.LastOrDefault() is not (ManagedThrow or ManagedRethrow or ManagedReturn or ManagedCall { Tail: true } or ManagedHole { Terminal: true }))
                exit = block.Successors.Count == 1 ? new Jump(block.End, block.Successors[0].Start) : Fail(block.End, "控制 块没有终结语句", terminal: true);
            lowered.Add((block, output, exit));
        }
        // φ 的闭包：入边赋值的来源可能用到新的 φ。
        var done = new HashSet<PhiSym>();
        var copies = new Dictionary<(Block From, Block To, int Index), List<ManagedCopy>>();
        current = EdgeUse;
        while (phis.Except(done).ToArray() is { Length: > 0 } pending)
            foreach (var phi in pending)
            {
                done.Add(phi);
                var local = locals[phi];
                for (var j = 0; j < phi.Block.Predecessors.Count; j++)
                {
                    var from = phi.Block.Predecessors[j];
                    var source = phi.Sources[j] is { } s ? View(s, local.Type, from.End) : Hole(from.End, "φ 来源缺失", local.Type);
                    if (!copies.TryGetValue((from, phi.Block, j), out var list)) copies[(from, phi.Block, j)] = list = [];
                    list.Add(new ManagedCopy(local, source));
                }
            }
        ManagedEdge Edge(Block from, ulong target)
        {
            var to = function.Blocks.FirstOrDefault(b => b.Start == target);
            if (to is null) return new ManagedEdge(target, []);
            var index = Enumerable.Range(0, to.Predecessors.Count).FirstOrDefault(j => to.Predecessors[j] == from, -1);
            return new ManagedEdge(target, index >= 0 && copies.TryGetValue((from, to, index), out var list) ? list : []);
        }
        var blocks = new List<ManagedBlock>();
        foreach (var (block, statements, exit) in lowered)
        {
            switch (exit)
            {
                case Jump jump: statements.Add(new ManagedJump(jump.Address, Edge(block, jump.Target))); break;
                case Branch branch: statements.Add(new ManagedBranch(branch.Address, branch.Condition, Edge(block, branch.Target), Edge(block, branch.Fallthrough))); break;
                case Statement statement: statements.Add(statement.Value); break;
            }
            blocks.Add(new ManagedBlock(block.Start, statements));
        }
        foreach (var (result, _) in constructions.Where(p => !locals.ContainsKey(p.Key)))
            holes.Add(new RecoveryHole(result.Site.Address, "构造 分配后没有构造函数调用"));
        var body = new ManagedBody(analysis.Method, blocks);
        return holes.Count == 0
            ? new(analysis.Method, analysis.Entry, body, [])
            : new(analysis.Method, analysis.Entry, null, holes.DistinctBy(h => (h.Address, h.Reason)).ToArray()) { Partial = body };
    }

    // ---- 终结语句 ----

    private abstract record Terminator;
    private sealed record Jump(ulong Address, ulong Target) : Terminator;
    private sealed record Branch(ulong Address, ManagedValue Condition, ulong Target, ulong Fallthrough) : Terminator;
    private sealed record Statement(ManagedStatement Value) : Terminator;

    private Terminator Fail(ulong address, string reason, bool terminal)
    {
        holes.Add(new RecoveryHole(address, reason));
        return new Statement(new ManagedHole(address, reason, terminal));
    }

    private ManagedValue Hole(ulong address, string reason, TypeRef? type)
    {
        holes.Add(new RecoveryHole(address, reason));
        var t = type ?? types.Object;
        return new HoleValue(reason, t, Width(t));
    }

    // ---- 读取的落点 ----

    /// <summary>空跑时记录：每个读取被哪些语句的 IL 值用到。</summary>
    private Dictionary<ReadSym, HashSet<Stmt>>? demand;
    private Stmt? current;
    private static readonly Stmt EdgeUse = new Nop(0, "φ 入边");

    private void Demand(ReadSym read)
    {
        if (demand is null || current is null) return;
        if (!demand.TryGetValue(read, out var users)) demand[read] = users = new(ReferenceEqualityComparer.Instance);
        users.Add(current);
    }

    // ---- 语句 ----

    private Terminator? Lower(Block block, int index, List<ManagedStatement> output)
    {
        var statement = block.Statements[index];
        var operands = values.Operands(statement);
        foreach (var read in Reads(statement).Where(materialized.Contains))
            if (Read(read, statement.Address) is { } value)
                output.Add(new ManagedAssignment(statement.Address, Local(read, value.Type), value));
        switch (statement)
        {
            case Define or Phi or Nop or Assign:
                return null;
            case Store store:
                {
                    var location = oracle.Locate(operands[0], store.Value.Width);
                    if (location is null) { output.Add(new ManagedHole(store.Address, $"内存 写入位置 {operands[0]}", false)); holes.Add(new(store.Address, $"内存 写入位置 {operands[0]}")); return null; }
                    output.Add(new ManagedStore(store.Address, LocationValue(location, store.Address), View(operands[1], location.Type, store.Address)));
                    return null;
                }
            case Call call:
                return LowerCall(block, index, call, operands, output);
            case Ir.Branch branch:
                return new Branch(branch.Address, View(operands[0], types.Boolean, branch.Address), branch.Target, branch.Fallthrough);
            case Ir.Jump jump:
                return new Jump(jump.Address, jump.Target);
            case Return ret:
                return new Statement(new ManagedReturn(ret.Address, ReturnValue(ret, operands)));
            case Trap trap:
                return Fail(trap.Address, $"控制 陷入 {trap.Kind}", terminal: true);
            case IndirectJump jump:
                return Fail(jump.Address, "控制 间接跳转尚未接入", terminal: true);
            default:
                return Fail(statement.Address, $"语句 {statement.GetType().Name}", terminal: false) is Statement s ? AddHole(output, s) : null;
        }
    }

    private static Terminator? AddHole(List<ManagedStatement> output, Statement hole)
    {
        output.Add(hole.Value);
        return null;
    }

    private IEnumerable<ReadSym> Reads(Stmt statement)
    {
        var found = new List<ReadSym>();
        void Walk(Sym sym, HashSet<Sym> seen)
        {
            sym = SymTable.Resolve(sym);
            if (!seen.Add(sym)) return;
            switch (sym)
            {
                case ReadSym read:
                    Walk(read.Address, seen);
                    if (ReferenceEquals(read.Site, statement)) found.Add(read);
                    break;
                case SliceSym slice: Walk(slice.Base, seen); break;
                case ConcatSym concat: foreach (var part in concat.Parts) Walk(part, seen); break;
                case OpSym op: foreach (var arg in op.Args) Walk(arg, seen); break;
            }
        }
        var visited = new HashSet<Sym>();
        foreach (var operand in values.Operands(statement)) Walk(operand, visited);
        return found.OrderBy(r => r.Ordinal);
    }

    private ManagedValue? ReturnValue(Return ret, IReadOnlyList<Sym> operands)
    {
        var type = oracle.ReturnType;
        if (ManagedTypes.IsVoid(type)) return null;
        if (ret.Pieces.Length == 0) return Hole(ret.Address, "返回 返回值缺失", type);
        var width = analysis.Signature.Return is { } r ? MethodEnvironment.ValueWidth(r) : Width(type);
        var bits = new Sym?[width];
        var parts = new List<Sym>();
        var at = 0;
        foreach (var (piece, sym) in ret.Pieces.Zip(operands.Skip(ret.Value is null ? 0 : 1)).OrderBy(p => p.First.Offset))
        {
            var start = piece.Offset * 8;
            if (start > at) parts.Add(values.Syms.Undef(start - at));
            if (start < at) continue;
            var size = Math.Min(sym.Width, width - start);
            parts.Add(values.Syms.Slice(sym, 0, size));
            at = start + size;
        }
        if (at < width) parts.Add(values.Syms.Undef(width - at));
        return View(values.Syms.Concat(parts), type, ret.Address);
    }

    // ---- 调用 ----

    private Terminator? LowerCall(Block block, int index, Call call, IReadOnlyList<Sym> operands, List<ManagedStatement> output)
    {
        var arguments = operands.Skip(1).Take(call.Arguments.Length).ToArray();
        var shape = analysis.Environment.Shape(call);
        if (call.Op is { } op && !shape.IsDispatch)
            return LowerRuntime(block, index, call, op, arguments, output);
        var signature = shape.Signature;
        if (signature is null)
        {
            output.Add(new ManagedHole(call.Address, "调用 目标或签名未知", false));
            holes.Add(new(call.Address, "调用 目标或签名未知"));
            return call.Kind is CallKind.Tail or CallKind.TailIndirect ? new Statement(new ManagedHole(call.Address, "调用 尾调用", true)) : null;
        }
        var contents = signature.Arguments.Select(v => Content(call, v, arguments)).ToArray();
        var callee = oracle.Callee(call);
        if (callee is null)
        {
            holes.Add(new(call.Address, "调用 目标未知"));
            return call.Kind is CallKind.Tail or CallKind.TailIndirect ? new Statement(new ManagedHole(call.Address, "调用 目标未知", true))
                : AddHole(output, new Statement(new ManagedHole(call.Address, "调用 目标未知", false)));
        }
        // 分配之后的实例构造：合为 newobj（委托为委托构造），接收者不作为值出现。
        var construction = callee.Method.Name == ".ctor" && !callee.Method.IsStatic && contents.Length > 0
            && SymTable.Resolve(contents[0]) is ResultSym { Site.Op.Kind: OpKind.NewObject } allocated && constructions.ContainsKey(allocated) ? allocated : null;
        var managed = new List<ManagedValue>();
        ManagedValue? receiver = null;
        for (var i = 0; i < signature.Arguments.Length; i++)
        {
            var value = signature.Arguments[i];
            if (value.Index < 0 && construction is not null) continue;
            var type = value.Index < 0 ? (callee.Method.Owner.IsValueType ? new ByRefRef(callee.DeclaringType) : callee.DeclaringType)
                : TypeOracle.Concrete(callee, callee.Method.Parameters[value.Index].Type);
            if (construction is not null && DelegateFacts.IsDelegate(callee.DeclaringType) && value.Index == 1
                && SymTable.Resolve(contents[i]) is EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef target } } && managed.Count == 1)
            {
                var created = new DelegateValue((DefinitionRef)callee.DeclaringType, managed[0], target, target.Method.IsStatic ? DelegateBinding.Static : DelegateBinding.ClosedInstance);
                output.Add(new ManagedAssignment(call.Address, Local(construction, callee.DeclaringType), created));
                return call.Kind == CallKind.Tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
            }
            var argument = value.Index < 0 && call.Op?.Kind == OpKind.CallDelegate && call.DelegateReceiver is not null
                ? View(operands[1 + call.Arguments.Length], type, call.Address)
                : Argument(call, value, type, contents[i], arguments, output);
            if (value.Index < 0) receiver = argument;
            else managed.Add(argument);
        }
        if (construction is not null)
        {
            output.Add(new ManagedAssignment(call.Address, Local(construction, callee.DeclaringType), new NewObjectValue(callee, managed)));
            return call.Kind == CallKind.Tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
        }
        var invocation = new ManagedInvocation(callee, receiver, managed, Virtual: receiver is not null && (shape.IsDispatch || absorbedChecks.Contains(contents[0])));
        LocalValue? result = null;
        var returnType = TypeOracle.Concrete(callee, callee.Method.ReturnType);
        if (!ManagedTypes.IsVoid(returnType))
            result = signature.Return?.Transfer == Transfer.ResultBuffer
                ? Local(values.Syms.Out(call, MachineSignature.ReturnIndex, MethodEnvironment.ValueWidth(signature.Return)), returnType)
                : Local(values.Syms.Result(call, 0, signature.Return is { } ret ? MethodEnvironment.ValueWidth(ret) : Width(returnType)), returnType);
        var tail = call.Kind is CallKind.Tail or CallKind.TailIndirect;
        var lowered = new ManagedCall(call.Address, invocation, tail ? null : result, tail);
        if (tail) return new Statement(lowered);
        output.Add(lowered);
        return null;
    }

    /// <summary>机器签名中一个值在调用处的内容：寄存器片与栈片按值中的位置拼接。</summary>
    private Sym Content(Call call, MachineValue value, IReadOnlyList<Sym> arguments)
    {
        var syms = values.Syms;
        var width = value.Transfer == Transfer.Value ? MethodEnvironment.ValueWidth(value) : 64;
        var parts = new SortedDictionary<int, Sym>();
        if (value.Transfer == Transfer.Value)
        {
            foreach (var piece in value.Pieces)
            {
                var position = Array.IndexOf(call.Sources, piece.Register);
                if (position >= 0) parts[piece.Offset * 8] = syms.Slice(arguments[position], 0, Math.Min(piece.Width, arguments[position].Width));
            }
            foreach (var access in call.Memory.Where(m => !m.Write && m.Value == value.Index))
                if (Array.IndexOf(call.Sources, access.Cell) is var cell and >= 0)
                    parts[access.ValueBit] = syms.Slice(arguments[cell], access.CellBit, access.Width);
        }
        else if (Array.IndexOf(call.Sources, value.Pieces[0].Register) is var pointer and >= 0)
            return arguments[pointer];
        if (parts.Count == 0) return syms.Unknown("实参缺失", width);
        var list = new List<Sym>();
        var at = 0;
        foreach (var (bit, part) in parts)
        {
            if (bit < at) continue;
            if (bit > at) list.Add(syms.Undef(bit - at));
            var size = Math.Min(part.Width, width - bit);
            if (size <= 0) break;
            list.Add(syms.Slice(part, 0, size));
            at = bit + size;
        }
        if (at < width) list.Add(syms.Undef(width - at));
        return syms.Concat(list);
    }

    /// <summary>
    /// 一个 IL 实参。按值传递时为内容的视图；按副本传递时为被指单元在调用前的内容；
    /// ref 实参指向已提升的单元时成为局部：调用前写入原内容，调用写出的值即该局部，再取其地址。
    /// </summary>
    private ManagedValue Argument(Call call, MachineValue value, TypeRef type, Sym content, IReadOnlyList<Sym> arguments, List<ManagedStatement> output)
    {
        switch (value.Transfer)
        {
            case Transfer.Value:
                return View(content, type, call.Address);
            case Transfer.Copy:
                {
                    var stored = CellContent(call, value, arguments, write: false);
                    if (stored is not null) return View(stored, type, call.Address);
                    return SymTable.Resolve(content) is var p && oracle.Locate(p, value.Size * 8) is { } location
                        ? LocationValue(location, call.Address) : Hole(call.Address, "调用 副本实参的内容未知", type);
                }
            case Transfer.Reference:
                {
                    var element = type is ByRefRef byRef ? byRef.Element : type;
                    if (SymTable.Resolve(content) is LocalSym)
                    {
                        var local = NewLocal(element);
                        if (CellContent(call, value, arguments, write: false) is { } before)
                            output.Add(new ManagedAssignment(call.Address, local, View(before, element, call.Address)));
                        if (call.Memory.Any(m => m.Write && m.Value == value.Index))
                            locals[values.Syms.Out(call, value.Index, value.Size * 8)] = local;
                        return new AddressValue(local);
                    }
                    if (oracle.TypeOf(content) is ByRefRef or PointerRef) return View(content, type, call.Address);
                    return oracle.Locate(content, Math.Max(8, value.Size * 8)) is { } target
                        ? new AddressValue(LocationValue(target, call.Address)) : Hole(call.Address, $"调用 ref 实参的位置 {content}", type);
                }
            default:
                return Hole(call.Address, $"调用 实参传递方式 {value.Transfer}", type);
        }
    }

    /// <summary>调用读取的单元中属于 value 的内容。</summary>
    private Sym? CellContent(Call call, MachineValue value, IReadOnlyList<Sym> arguments, bool write)
    {
        var accesses = call.Memory.Where(m => m.Write == write && m.Value == value.Index).OrderBy(m => m.ValueBit).ToArray();
        if (accesses.Length == 0) return null;
        var syms = values.Syms;
        var parts = new List<Sym>();
        var at = 0;
        var width = accesses[0].ValueWidth;
        foreach (var access in accesses)
        {
            if (access.ValueBit < at) continue;
            if (access.ValueBit > at) parts.Add(syms.Undef(access.ValueBit - at));
            var position = Array.IndexOf(call.Sources, access.Cell);
            if (position < 0) return null;
            parts.Add(syms.Slice(arguments[position], access.CellBit, access.Width));
            at = access.ValueBit + access.Width;
        }
        if (at < width) parts.Add(syms.Undef(width - at));
        return syms.Concat(parts);
    }

    private Terminator? LowerRuntime(Block block, int index, Call call, RuntimeOp op, IReadOnlyList<Sym> arguments, List<ManagedStatement> output)
    {
        var result = values.Syms.Result(call, 0, 64);
        var tail = call.Kind is CallKind.Tail or CallKind.TailIndirect;
        switch (op.Kind)
        {
            case OpKind.WriteBarrier or OpKind.MemoryBarrier or OpKind.InitClass or OpKind.RunClassConstructor or OpKind.InitMethodRgctx:
                return tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
            // 只服务于分派：结果只流向调用目标与 MethodInfo，不是 IL 值。
            case OpKind.InterfaceInvokeData or OpKind.ResolveGenericVirtual:
                return null;
            case OpKind.NullCheck when arguments.Count == 1:
                {
                    var target = SymTable.Resolve(arguments[0]);
                    if (Absorbed(block, index + 1, target)) { absorbedChecks.Add(target); return null; }
                    if (types.CorlibMethod("System.NullReferenceException", ".ctor") is { } nre)
                        output.Add(new ManagedCheck(call.Address, new ComparisonValue(Cond.Eq, View(target, types.Object, call.Address), new ConstantValue(0, types.Object, 64), types.Boolean), nre));
                    else output.Add(new ManagedHole(call.Address, "检查 缺少 NullReferenceException", false));
                    return null;
                }
            case OpKind.NewObject when op.Operand is TypeRef created:
                constructions[result] = call;
                return null;
            case OpKind.NewArray when op.Operand is ArrayRef array && arguments.Count == 2:
                output.Add(new ManagedAssignment(call.Address, Local(result, array), new NewArrayValue(array, View(arguments[1], types.Int32, call.Address))));
                return null;
            case OpKind.Box when op.Operand is TypeRef boxed && arguments.Count == 2:
                {
                    var content = call.Memory.Where(m => !m.Write && m.Value == 1).ToArray() is { Length: > 0 } reads
                        ? values.Syms.Concat(reads.OrderBy(m => m.ValueBit).Select(m => values.Syms.Slice(arguments[Array.IndexOf(call.Sources, m.Cell)], m.CellBit, m.Width)))
                        : null;
                    var operand = content is not null ? View(content, boxed, call.Address)
                        : oracle.Locate(arguments[1], Width(boxed)) is { } location ? LocationValue(location, call.Address) : Hole(call.Address, "装箱 值的位置未知", boxed);
                    output.Add(new ManagedAssignment(call.Address, Local(result, types.Object), new BoxValue(operand, boxed, types.Object)));
                    return null;
                }
            case OpKind.Unbox when op.Operand is TypeRef unboxed && arguments.Count == 2:
                output.Add(new ManagedAssignment(call.Address, Local(result, new ByRefRef(unboxed)), new UnboxAddressValue(View(arguments[1], types.Object, call.Address), unboxed)));
                return null;
            case OpKind.IsInst when op.Operand is TypeRef target && arguments.Count >= 1:
                output.Add(new ManagedAssignment(call.Address, Local(result, target), new IsInstValue(View(arguments[0], types.Object, call.Address), target)));
                return null;
            case OpKind.Throw when arguments.Count >= 1:
                return new Statement(new ManagedThrow(call.Address, View(arguments[0], types.Object, call.Address)));
            case OpKind.ThrowNew when op.Operand is string name && Constructor(name) is { } ctor:
                return new Statement(new ManagedThrow(call.Address, new NewObjectValue(ctor, [])));
            case OpKind.NewException when op.Operand is string name && Constructor(name) is { } ctor:
                output.Add(new ManagedAssignment(call.Address, Local(result, ctor.DeclaringType), new NewObjectValue(ctor, [])));
                return null;
            case OpKind.ThrowIf when op.Operand is string name && arguments.Count == 1 && Constructor(name) is { } ctor:
                output.Add(new ManagedCheck(call.Address, View(arguments[0], types.Boolean, call.Address), ctor));
                return null;
            case OpKind.BoundsCheck when arguments.Count == 2 && Constructor("System.IndexOutOfRangeException") is { } ctor:
                output.Add(new ManagedCheck(call.Address, new ComparisonValue(Cond.Uge, View(arguments[0], types.Int32, call.Address), View(arguments[1], types.Int32, call.Address), types.Boolean), ctor));
                return null;
            case OpKind.Rethrow:
                return new Statement(new ManagedRethrow(call.Address));
        }
        holes.Add(new(call.Address, $"运行时 {op.Kind}"));
        if (tail) return new Statement(new ManagedHole(call.Address, $"运行时 {op}", true));
        output.Add(new ManagedHole(call.Address, $"运行时 {op}", false));
        return null;
    }

    private MethodRef? Constructor(string exception) => oracle.ExceptionType(exception) is { } type
        ? type.Definition.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0) is { } ctor ? new MethodRef(ctor, [], []) : null
        : null;

    /// <summary>
    /// 判空被吸收：直线路径上判空之后第一个有副作用的语句经该对象访问字段、元素或调用其实例方法——
    /// ldfld、ldelem 与 callvirt 对 null 抛出同一异常。
    /// </summary>
    private bool Absorbed(Block block, int index, Sym target)
    {
        for (var steps = 0; steps < 64; steps++)
        {
            if (index >= block.Statements.Count)
            {
                if (block.Successors.Count != 1 || block.Successors[0].Predecessors.Count != 1 || block.Handler is not null) return false;
                block = block.Successors[0];
                index = 0;
                continue;
            }
            var statement = block.Statements[index++];
            if (statement is Nop or Phi || statement is Ir.Jump) continue;
            var reads = Reads(statement).ToArray();
            if (reads.Length > 0) return reads.Any(r => ReferenceEquals(oracle.Decompose(r.Address).Root, target));
            switch (statement)
            {
                case Define: continue;
                case Store store: return ReferenceEquals(oracle.Decompose(values.Operands(store)[0]).Root, target);
                case Call { Op: null } call:
                    {
                        var operands = values.Operands(call);
                        return call.Arguments.Length > 0 && ReferenceEquals(SymTable.Resolve(operands[1]), target);
                    }
                case Call { Op.Kind: OpKind.NullCheck or OpKind.WriteBarrier }: continue;
                default: return false;
            }
        }
        return false;
    }

    // ---- 值 ----

    private LocalValue NewLocal(TypeRef type) => new(new Variable(Storage.Temp(1000 + nextLocal++), 1), type, Width(type));

    private LocalValue Local(Sym sym, TypeRef type)
    {
        sym = SymTable.Resolve(sym);
        if (!locals.TryGetValue(sym, out var local)) locals[sym] = local = NewLocal(type);
        return local;
    }

    private int Width(TypeRef type) => ManagedTypes.IsReferenceType(type) || type is ByRefRef or PointerRef ? 64
        : types.Kind(type) == TypeKind.Struct ? 0 : Math.Max(1, types.Bits(type));

    private ManagedValue? Read(ReadSym read, ulong address)
    {
        if (oracle.Locate(read.Address, read.Width) is not { } location) return Hole(address, $"内存 读取位置 {read.Address}", null);
        return LocationValue(location, address);
    }

    private ManagedValue LocationValue(Location location, ulong address)
    {
        ManagedValue value;
        var path = location.Path;
        TypeRef Leaf(int i) => i == path.Count - 1 ? location.Type : path[i].Field.Type.Substitute(((DefinitionRef)path[i].DeclaringType).Arguments, []);
        switch (location.Kind)
        {
            case LocationKind.Static or LocationKind.ThreadStatic:
                value = new StaticFieldValue(path[0], Leaf(0), Width(Leaf(0)));
                path = path.Skip(1).ToArray();
                return Nest(value, path, location.Type);
            case LocationKind.Instance:
                return Nest(View(location.Base!, oracle.TypeOf(location.Base!), address), path, location.Type);
            case LocationKind.Reference:
                {
                    var pointer = View(location.Base!, oracle.TypeOf(location.Base!), address);
                    if (path.Count == 0) return new IndirectValue(pointer, location.Type, Width(location.Type));
                    return Nest(pointer, path, location.Type);
                }
            case LocationKind.Element:
                {
                    var array = View(location.Base!, oracle.TypeOf(location.Base!), address);
                    var index = location.Index is { } i ? View(i, types.Int32, address) : new ConstantValue((ulong)location.ConstantIndex, types.Int32, 32);
                    var element = array.Type is ArrayRef a ? a.Element : location.Type;
                    value = new ArrayElementValue(array, index, element, Width(element));
                    return Nest(value, path, location.Type);
                }
            case LocationKind.Length:
                return new ArrayLengthValue(View(location.Base!, oracle.TypeOf(location.Base!), address), types.Int32, 32);
        }
        return Hole(address, $"内存 位置 {location.Kind} 尚未接入", location.Type);
    }

    private ManagedValue Nest(ManagedValue receiver, IReadOnlyList<FieldRef> path, TypeRef leaf)
    {
        var value = receiver;
        for (var i = 0; i < path.Count; i++)
        {
            var type = i == path.Count - 1 ? leaf : path[i].Field.Type.Substitute(((DefinitionRef)path[i].DeclaringType).Arguments, []);
            value = new FieldValue(value, path[i], type, Width(type));
        }
        return value;
    }

    /// <summary>符号值在期望类型下的托管视图。</summary>
    private ManagedValue View(Sym sym, TypeRef? expected, ulong address)
    {
        sym = SymTable.Resolve(sym);
        if (locals.TryGetValue(sym, out var known)) return Coerce(known, expected);
        switch (sym)
        {
            case ArgSym arg:
                {
                    var type = oracle.Parameter(arg.Index)!;
                    return Coerce(new ArgumentValue(arg.Index, type, Width(type)), expected);
                }
            case ConstSym constant:
                return Constant(constant, expected);
            case EntitySym { Symbol: { Kind: SymbolKind.String, Value: string text } }:
                return new StringValue(text, types.String);
            case ReadSym read:
                Demand(read);
                return Read(read, address) is { } value ? Coerce(value, expected) : Hole(address, "内存 读取", expected);
            case ResultSym result when constructions.ContainsKey(result):
                return Hole(address, "构造 对象在构造函数调用前被使用", expected);
            case PhiSym phi:
                {
                    var type = oracle.TypeOf(phi) ?? expected;
                    if (type is null) return Hole(address, "类型 φ 没有类型", expected);
                    phis.Add(phi);
                    return Coerce(Local(phi, type), expected);
                }
            case OpSym op:
                return Coerce(Operation(op, expected, address), expected);
            case SliceSym slice:
                return Slice(slice, expected, address);
            case ConcatSym concat:
                return Composite(concat, expected, address);
            case UndefSym:
                return Hole(address, "值 未定义", expected);
            case UnknownSym unknown:
                return Hole(address, $"值 {unknown.Reason}", expected);
        }
        return Hole(address, $"值 {sym}", expected);
    }

    private ManagedValue Coerce(ManagedValue value, TypeRef? expected)
    {
        if (expected is null || value.Type.Equals(expected) || value is HoleValue) return value;
        if (ManagedTypes.IsReferenceType(value.Type) && ManagedTypes.IsReferenceType(expected)) return value;
        var (from, to) = (types.Kind(value.Type), types.Kind(expected));
        if (from is TypeKind.Int or TypeKind.Bool && to is TypeKind.Int or TypeKind.Bool)
        {
            var (a, b) = (Width(value.Type), Width(expected));
            if (a == b || to == TypeKind.Bool && value.Width == 1) return value;
            return new ConversionValue(a < b ? (ManagedTypes.IsSigned(value.Type) ? ConvKind.SignExtend : ConvKind.ZeroExtend) : ConvKind.Truncate, value, expected, b);
        }
        return value;
    }

    private ManagedValue Constant(ConstSym constant, TypeRef? expected)
    {
        if (expected is not null)
        {
            if ((ManagedTypes.IsReferenceType(expected) || expected is PointerRef or ByRefRef) && constant.Value == 0) return new ConstantValue(0, expected, 64);
            switch (types.Kind(expected))
            {
                case TypeKind.Bool: return new ConstantValue(constant.Value != 0 ? 1UL : 0UL, expected, 8);
                case TypeKind.Int or TypeKind.Float or TypeKind.Double or TypeKind.Pointer:
                    return new ConstantValue(constant.Value & Expr.Mask(Width(expected)), expected, Width(expected));
            }
        }
        return constant.Width switch
        {
            1 => new ConstantValue(constant.Value, types.Boolean, 8),
            8 or 16 or 32 or 64 => new ConstantValue(constant.Value, types.Integer(constant.Width, true), constant.Width),
            _ => new ConstantValue(constant.Value, types.Int64, 64),
        };
    }

    private ManagedValue Operation(OpSym op, TypeRef? expected, ulong address)
    {
        var natural = oracle.TypeOf(op);
        switch (op.Op.Kind)
        {
            case OperatorKind.Compare:
                {
                    var hint = oracle.TypeOf(op.Args[0]) ?? oracle.TypeOf(op.Args[1]);
                    return new ComparisonValue(op.Op.Cond, View(op.Args[0], hint, address), View(op.Args[1], hint, address), types.Boolean);
                }
            case OperatorKind.And or OperatorKind.Or:
                return new BooleanValue(op.Op.Kind == OperatorKind.And, View(op.Args[0], types.Boolean, address), View(op.Args[1], types.Boolean, address), types.Boolean);
            case OperatorKind.Not:
                return new NegatedValue(View(op.Args[0], types.Boolean, address), types.Boolean);
            case OperatorKind.Select:
                {
                    var type = natural ?? expected ?? types.Integer(op.Width is 8 or 16 or 32 or 64 ? op.Width : 64, true);
                    return new ChoiceValue(View(op.Args[0], types.Boolean, address), View(op.Args[1], type, address), View(op.Args[2], type, address), type, Width(type));
                }
            case OperatorKind.Binary:
                {
                    var type = expected is not null && types.Kind(expected) is TypeKind.Int && Width(expected) == op.Width ? expected : natural;
                    if (type is null) return Hole(address, $"类型 运算 {op.Op}", expected);
                    return new BinaryValue(op.Op.Binary, View(op.Args[0], type, address), View(op.Args[1], op.Op.Binary is BinOp.Shl or BinOp.LShr or BinOp.AShr ? types.Int32 : type, address), type, op.Width);
                }
            case OperatorKind.Unary:
                {
                    var type = natural ?? expected;
                    if (type is null) return Hole(address, $"类型 运算 {op.Op}", expected);
                    return new UnaryValue(op.Op.Unary, View(op.Args[0], type, address), type, op.Width);
                }
            case OperatorKind.Convert:
                {
                    var type = natural ?? (expected is not null && Width(expected) == op.Width ? expected : null);
                    if (type is null) return Hole(address, $"类型 转换 {op.Op}", expected);
                    var operandWidth = op.Args[0].Width;
                    var source = op.Op.Conversion switch
                    {
                        ConvKind.FloatToFloat or ConvKind.FloatToSInt or ConvKind.FloatToUInt => operandWidth == 32 ? types.Single : types.Double,
                        ConvKind.SIntToFloat or ConvKind.SignExtend when operandWidth is 8 or 16 or 32 or 64 => oracle.TypeOf(op.Args[0]) is { } t && types.Kind(t) is TypeKind.Int ? t : types.Integer(operandWidth, true),
                        ConvKind.UIntToFloat when operandWidth is 8 or 16 or 32 or 64 => types.Integer(operandWidth, false),
                        _ => oracle.TypeOf(op.Args[0]),
                    };
                    return new ConversionValue(op.Op.Conversion, View(op.Args[0], source, address), type, op.Width);
                }
        }
        return Hole(address, $"运算 {op.Op} 尚未接入", expected);
    }

    /// <summary>原子的一段：值类型的字段；整数的低位截断；bool 的低位即自身。</summary>
    private ManagedValue Slice(SliceSym slice, TypeRef? expected, ulong address)
    {
        var baseType = oracle.TypeOf(slice.Base);
        if (baseType is null) return Hole(address, $"类型 切片的来源 {slice.Base}", expected);
        var source = View(slice.Base, baseType, address);
        switch (types.Kind(baseType))
        {
            case TypeKind.Struct:
                return oracle.FieldAt(baseType, slice.Low / 8 + RuntimeLayout.ObjectHeaderSize, slice.Width, false, false) is var (path, type) && slice.Low % 8 == 0
                    ? Coerce(Nest(source, path, type), expected) : Hole(address, $"值 结构体 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
            case TypeKind.Bool when slice.Low == 0:
                return source;
            case TypeKind.Int or TypeKind.Pointer when slice.Width is 8 or 16 or 32 or 64:
                {
                    var target = expected is not null && types.Kind(expected) is TypeKind.Int or TypeKind.Bool && Width(expected) == slice.Width ? expected : types.Integer(slice.Width, false);
                    ManagedValue shifted = slice.Low == 0 ? source : new BinaryValue(BinOp.LShr, source, new ConstantValue((ulong)slice.Low, types.Int32, 32), baseType, Width(baseType));
                    return new ConversionValue(ConvKind.Truncate, shifted, target, slice.Width);
                }
            case TypeKind.Int when slice.Width == 1 && slice.Low == 0:
                return new ComparisonValue(Cond.Ne, new BinaryValue(BinOp.And, source, new ConstantValue(1, baseType, Width(baseType)), baseType, Width(baseType)), new ConstantValue(0, baseType, Width(baseType)), types.Boolean);
        }
        return Hole(address, $"值 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
    }

    /// <summary>拼接按期望类型解释：结构体按字段组成；整数为零扩展；bool 的零扩展即自身。</summary>
    private ManagedValue Composite(ConcatSym concat, TypeRef? expected, ulong address)
    {
        if (expected is null && concat.Parts.Skip(1).All(p => p is ConstSym { Value: 0 }) && concat.Width is 8 or 16 or 32 or 64)
            expected = types.Integer(concat.Width, false);
        if (expected is null) return Hole(address, $"类型 拼接没有期望类型 {concat}", null);
        var syms = values.Syms;
        switch (types.Kind(expected))
        {
            case TypeKind.Struct when expected is DefinitionRef structure:
                {
                    var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
                    foreach (var (path, type, offset) in Leaves(structure, 0))
                    {
                        var width = Width(type);
                        if (offset * 8 + width > concat.Width) return Hole(address, $"值 {expected} 超出拼接宽度", expected);
                        leaves.Add((path, View(syms.Slice(concat, offset * 8, width), type, address)));
                    }
                    return new ComposedValue(expected, leaves);
                }
            case TypeKind.Int or TypeKind.Bool or TypeKind.Pointer:
                {
                    var parts = concat.Parts;
                    var low = parts[0];
                    var high = parts.Skip(1).ToArray();
                    if (parts[0] is ConstSym { Value: 0 } && parts.Length == 2 && parts[1] is SliceSym { Low: 0 } shifted && shifted.Base.Width == concat.Width
                        && oracle.TypeOf(shifted.Base) is { } shiftedType && types.Kind(shiftedType) is TypeKind.Int)
                        return Coerce(new BinaryValue(BinOp.Shl, View(shifted.Base, shiftedType, address), new ConstantValue((ulong)parts[0].Width, types.Int32, 32), shiftedType, concat.Width), expected);
                    if (high.All(p => p is ConstSym { Value: 0 } or UndefSym))
                    {
                        var lowType = oracle.TypeOf(low);
                        if (lowType is not null && types.Kind(lowType) == TypeKind.Bool) return View(low, expected, address);
                        var narrow = low.Width is 8 or 16 or 32 or 64 ? types.Integer(low.Width, false) : low.Width == 1 ? types.Boolean : null;
                        if (narrow is null) return Hole(address, $"值 拼接的低段宽 {low.Width}", expected);
                        var inner = View(low, lowType is not null && types.Kind(lowType) is TypeKind.Int ? lowType : narrow, address);
                        return high.All(p => p is UndefSym) ? Coerce(inner, expected) : new ConversionValue(ConvKind.ZeroExtend, inner, expected, Width(expected));
                    }
                    break;
                }
        }
        return Hole(address, $"值 拼接 {concat} 作为 {expected}", expected);
    }

    /// <summary>值类型的标量叶子字段：路径、类型与相对值起点的字节偏移。</summary>
    private IEnumerable<(IReadOnlyList<FieldRef> Path, TypeRef Type, int Offset)> Leaves(DefinitionRef structure, int at)
    {
        if (types.Layouts.Of(structure) is not { } layout) yield break;
        foreach (var slot in layout.Fields.OrderBy(f => f.Offset))
        {
            var offset = at + slot.Offset - RuntimeLayout.ObjectHeaderSize;
            var field = new FieldRef(slot.Field, structure);
            if (types.Kind(slot.Type) == TypeKind.Struct && slot.Type is DefinitionRef inner)
                foreach (var (path, type, leaf) in Leaves(inner, offset)) yield return ([field, .. path], type, leaf);
            else yield return ([field], slot.Type, offset);
        }
    }
}
