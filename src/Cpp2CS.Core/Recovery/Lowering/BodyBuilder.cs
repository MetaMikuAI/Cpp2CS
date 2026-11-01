using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Runtime;
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
    private readonly Dictionary<Call, LocalValue> exceptions = new(ReferenceEqualityComparer.Instance);
    private IReadOnlyList<ExceptionRegionPlan> regions = [];
    private IReadOnlyList<Block> order = [];
    private Block? currentBlock;
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
        if (!ExceptionRegions.Build(function).TryGet(out var plan, out var failure))
            return new(analysis.Method, analysis.Entry, null, [new(failure.Address, failure.Reason)]);
        regions = plan.Regions;
        order = plan.Order;
        // 读取只在被所在语句之外的 IL 值用到时落成局部：先空跑一遍记录用途，再正式下降。
        demand = [];
        LowerBlocks();
        var users = demand;
        demand = null;
        foreach (var (read, set) in users)
            if (set.Any(user => !ReferenceEquals(user, read.Site))) materialized.Add(read);
        locals.Clear(); phis.Clear(); holes.Clear(); constructions.Clear(); absorbedChecks.Clear(); exceptions.Clear(); nextLocal = 0;
        return LowerBlocks();
    }

    private MethodRecoveryResult LowerBlocks()
    {
        var function = analysis.Function;
        foreach (var region in regions.Where(r => r.BeginCatch is not null))
            exceptions[region.BeginCatch!] = NewLocal(types.Corlib("System.Exception"));
        var lowered = new List<(Block Block, List<ManagedStatement> Statements, Terminator? Exit)>();
        foreach (var block in order)
        {
            var output = new List<ManagedStatement>();
            Terminator? exit = null;
            currentBlock = block;
            for (var i = 0; i < block.Statements.Count && exit is null; i++)
            {
                current = block.Statements[i];
                exit = Lower(block, i, output);
            }
            var normal = block.NormalSuccessors.ToArray();
            if (exit is null && output.LastOrDefault() is not (ManagedThrow or ManagedRethrow or ManagedReturn or ManagedEndFault or ManagedCall { Tail: true } or ManagedHole { Terminal: true }))
                exit = normal.Length == 1 ? new Jump(block.End, normal[0].Start) : Fail(block.End, "控制 块没有终结语句", terminal: true);
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
            // 异常边的 φ 赋值放在可能抛出的调用之前：异常经调用离开时局部已持有入边的值。
            if (block.Handler is { } pad && pad.Predecessors.IndexOf(block) is var padIndex and >= 0
                && copies.TryGetValue((block, pad, padIndex), out var exceptional) && exceptional.Count > 0)
            {
                var at = statements.FindLastIndex(s => s is ManagedCall);
                statements.InsertRange(at < 0 ? statements.Count : at, exceptional.Select(c => (ManagedStatement)new ManagedAssignment(block.End, c.Target, c.Value)));
            }
            switch (exit)
            {
                case Jump jump: statements.Add(new ManagedJump(jump.Address, Edge(block, jump.Target))); break;
                case Branch branch: statements.Add(new ManagedBranch(branch.Address, branch.Condition, Edge(block, branch.Target), Edge(block, branch.Fallthrough))); break;
                case Statement statement: statements.Add(statement.Value); break;
                case Switch table: statements.Add(new ManagedSwitch(table.Address, table.Index, table.Targets.Select(t => Edge(block, t)).ToArray())); break;
            }
            blocks.Add(new ManagedBlock(block.Start, statements));
        }
        foreach (var (result, _) in constructions.Where(p => !locals.ContainsKey(p.Key)))
            holes.Add(new RecoveryHole(result.Site.Address, "构造 分配后没有构造函数调用"));
        var managedRegions = regions.Select(r => new ManagedRegion(r.Try.Select(b => b.Start).ToArray(), r.Pad.Start, r.Handler.Select(b => b.Start).ToArray(),
            r.BeginCatch is { } begin ? exceptions[begin] : null, r.IsCatch ? ManagedRegionKind.Catch : ManagedRegionKind.Fault)).ToArray();
        var body = new ManagedBody(analysis.Method, blocks) { Regions = managedRegions };
        return holes.Count == 0
            ? new(analysis.Method, analysis.Entry, body, [])
            : new(analysis.Method, analysis.Entry, null, holes.DistinctBy(h => (h.Address, h.Reason)).ToArray()) { Partial = body };
    }

    // ---- 终结语句 ----

    private abstract record Terminator;
    private sealed record Jump(ulong Address, ulong Target) : Terminator;
    private sealed record Branch(ulong Address, ManagedValue Condition, ulong Target, ulong Fallthrough) : Terminator;
    private sealed record Statement(ManagedStatement Value) : Terminator;
    private sealed record Switch(ulong Address, ManagedValue Index, ulong[] Targets) : Terminator;

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
                    if (location is null && oracle.Split(operands[0], store.Value.Width) is { } leaves)
                    {
                        // 跨字段的写入按布局拆为逐字段写入（寄存器对、清零等一次写入多个字段）。
                        foreach (var (leaf, bit) in leaves)
                        {
                            var leafTarget = LocationValue(leaf, store.Address, store: true);
                            var leafValue = View(values.Syms.Slice(operands[1], bit, Width(leaf.Type)), leaf.Type, store.Address);
                            output.Add(leafTarget is LocalValue leafLocal ? new ManagedAssignment(store.Address, leafLocal, leafValue) : new ManagedStore(store.Address, leafTarget, leafValue));
                        }
                        return null;
                    }
                    if (location is null) { output.Add(new ManagedHole(store.Address, $"内存 写入位置 {operands[0]}", false)); holes.Add(new(store.Address, $"内存 写入位置 {operands[0]}")); return null; }
                    var target = LocationValue(location, store.Address, store: true);
                    var stored = View(operands[1], location.Type, store.Address);
                    output.Add(target is LocalValue whole ? new ManagedAssignment(store.Address, whole, stored) : new ManagedStore(store.Address, target, stored));
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
            case IndirectJump { Targets.Length: > 0 } jump when TableIndex(operands[0]) is { } tableIndex:
                return new Switch(jump.Address, View(tableIndex, types.Int32, jump.Address), jump.Targets);
            case IndirectJump jump:
                return Fail(jump.Address, "控制 间接跳转的目标集合或下标未知", terminal: true);
            default:
                return Fail(statement.Address, $"语句 {statement.GetType().Name}", terminal: false) is Statement s ? AddHole(output, s) : null;
        }
    }

    /// <summary>跳转表的下标：目标中唯一一次读取的地址为常量表基址加比例下标。</summary>
    private Sym? TableIndex(Sym target)
    {
        var stack = new Stack<Sym>();
        stack.Push(target);
        Sym? found = null;
        while (stack.Count > 0)
        {
            switch (SymTable.Resolve(stack.Pop()))
            {
                case ReadSym read:
                    if (found is not null) return null;
                    // 表基址为常量：比例下标，或唯一的变量项（字节表的比例为 1）。
                    var (root, _, index, _) = oracle.Decompose(read.Address);
                    index ??= root is ConstSym || ReferenceEquals(root, SymTable.Resolve(read.Address)) ? null : root;
                    if (index is null) return null;
                    found = index;
                    break;
                case SliceSym slice: stack.Push(slice.Base); break;
                case ConcatSym concat: foreach (var part in concat.Parts) stack.Push(part); break;
                case OpSym op: foreach (var arg in op.Args) stack.Push(arg); break;
            }
        }
        return found;
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
                : Unconstrained(shape, value, type, contents[i]) ?? Argument(call, value, type, contents[i], arguments, output);
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

    /// <summary>
    /// 被调方不读取的按值实参：原生代码不维护这些寄存器，内容与参数类型不兼容时，接收者取类型兼容的 this，其他取默认值。
    /// 这是推断：被调方的行为与该实参无关，任何类型正确的值都等价。
    /// </summary>
    private ManagedValue? Unconstrained(Calls.CallShape shape, MachineValue value, TypeRef type, Sym content)
    {
        if (value.Transfer != Transfer.Value || value.Pieces.Length == 0 || !value.Pieces.All(p => shape.Unused.Contains(p.Register))) return null;
        if (oracle.TypeOf(content) is { } actual && (actual.Equals(type) || types.IsAssignable(actual, type))) return null;
        if (value.Index < 0 && oracle.Parameter(-1) is { } self && (self.Equals(type) || types.IsAssignable(self, type)))
            return new ArgumentValue(-1, self, Width(self));
        return ManagedTypes.IsReferenceType(type) || types.Kind(type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Pointer
            ? new ConstantValue(0, type, Width(type)) : null;
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
                    var elementBits = types.Kind(element) == TypeKind.Struct ? types.Size(element) * 8 : Math.Max(8, Width(element));
                    if (SymTable.Resolve(content) is LocalSym escaped && analysis.Memory.Find(escaped.Space, escaped.Offset, 1) is { Promoted: false })
                        return oracle.Locate(escaped, elementBits) is { } escapedLocation
                            ? new AddressValue(LocationValue(escapedLocation, call.Address)) : Hole(call.Address, $"调用 ref 实参指向的可寻址局部 {escaped}", type);
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
        var tail = call.Kind is CallKind.Tail or CallKind.TailIndirect;
        var context = new RuntimeContext(this, block, index, call, op, arguments, output);
        if (RuntimeOps.Of(op.Kind)?.Lower is { } lower && lower(context, out var terminal))
            return terminal is not null ? new Statement(terminal) : tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
        holes.Add(new(call.Address, $"运行时 {op.Kind}"));
        if (tail) return new Statement(new ManagedHole(call.Address, $"运行时 {op}", true));
        output.Add(new ManagedHole(call.Address, $"运行时 {op}", false));
        return null;
    }

    /// <summary>运行时操作下降的上下文。</summary>
    private sealed class RuntimeContext(BodyBuilder owner, Block block, int index, Call call, RuntimeOp op, IReadOnlyList<Sym> arguments, List<ManagedStatement> output) : IRuntimeLowering
    {
        public ManagedTypes Types => owner.types;
        public Call Call => call;
        public RuntimeOp Op => op;
        public IReadOnlyList<Sym> Arguments => arguments;
        public Sym Result => owner.values.Syms.Result(call, 0, 64);
        public ManagedValue View(Sym sym, TypeRef? expected) => owner.View(sym, expected, call.Address);
        public LocalValue Local(Sym sym, TypeRef type) => owner.Local(sym, type);
        public void Emit(ManagedStatement statement) => output.Add(statement);
        public void AwaitConstruction() => owner.constructions[(ResultSym)Result] = call;
        public MethodRef? ExceptionConstructor(string fullName) => owner.Constructor(fullName);
        public ManagedValue Hole(string reason, TypeRef? type) => owner.Hole(call.Address, reason, type);

        public bool InFault => owner.regions.Any(r => !r.IsCatch && r.Handler.Contains(block));

        public Sym? ClassOwner(Sym klass) => owner.ClassOwner(klass);

        public bool InCatchOf(Sym exception) => owner.regions.Any(r => r.IsCatch && r.Handler.Contains(block)
            && SymTable.Resolve(exception) is ReadSym read && owner.oracle.Decompose(read.Address) is (ResultSym { Site: var begin }, 0, null, _) && ReferenceEquals(begin, r.BeginCatch));

        public bool Absorb(Sym target)
        {
            if (!owner.Absorbed(block, index + 1, target)) return false;
            owner.absorbedChecks.Add(target);
            return true;
        }

        public Sym? Pointee(int value)
        {
            var reads = call.Memory.Where(m => !m.Write && m.Value == value).OrderBy(m => m.ValueBit).ToArray();
            if (reads.Length == 0) return null;
            var syms = owner.values.Syms;
            return syms.Concat(reads.Select(m => syms.Slice(arguments[Array.IndexOf(call.Sources, m.Cell)], m.CellBit, m.Width)));
        }

        public ManagedValue? Location(int argument, TypeRef type) =>
            argument < arguments.Count && owner.oracle.Locate(arguments[argument], owner.Width(type)) is { } location ? owner.LocationValue(location, call.Address) : null;
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

    /// <summary>类指针所属的对象：引用类型对象偏移 0 处的 64 位读取。</summary>
    private Sym? ClassOwner(Sym klass) => SymTable.Resolve(klass) is ReadSym { Width: 64 } read
        && oracle.Decompose(read.Address) is (var root, 0, null, _) && oracle.TypeOf(root) is { } type && ManagedTypes.IsReferenceType(type) ? root : null;

    /// <summary>地址逃逸的单元对应的可寻址局部。</summary>
    private LocalValue CellLocal(LocalSym root)
    {
        if (!locals.TryGetValue(root, out var local))
        {
            var cell = analysis.Memory.Find(root.Space, root.Offset, 1)!;
            locals[root] = local = NewLocal(oracle.CellType(cell)!);
        }
        return local;
    }

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
        if (oracle.Decompose(read.Address) is (ResultSym { Site: { Op.Kind: OpKind.BeginCatch } begin }, 0, null, _) && exceptions.TryGetValue(begin, out var exception))
            return exception;
        if (oracle.Locate(read.Address, read.Width) is not { } location) return Hole(address, $"内存 读取位置 {read.Address}", null);
        return LocationValue(location, address);
    }

    /// <summary>
    /// 位置的托管值。写入目标（store）中值类型的根与中间字段以地址给出：stfld 需要对象引用或托管地址。
    /// </summary>
    private ManagedValue LocationValue(Location location, ulong address, bool store = false)
    {
        var path = location.Path;
        switch (location.Kind)
        {
            case LocationKind.Static or LocationKind.ThreadStatic:
                {
                    var type = FieldType(path[0], path.Count == 1 ? location.Type : null);
                    ManagedValue root = new StaticFieldValue(path[0], type, Width(type));
                    return path.Count == 1 ? root : Nest(store ? new AddressValue(root) : root, path.Skip(1).ToArray(), location.Type, store);
                }
            case LocationKind.Instance:
                return Nest(View(location.Base!, oracle.TypeOf(location.Base!), address), path, location.Type, store);
            case LocationKind.Reference:
                {
                    var pointer = View(location.Base!, oracle.TypeOf(location.Base!), address);
                    return path.Count == 0 ? new IndirectValue(pointer, location.Type, Width(location.Type)) : Nest(pointer, path, location.Type, store);
                }
            case LocationKind.Element:
                {
                    var array = View(location.Base!, oracle.TypeOf(location.Base!), address);
                    var index = location.Index is { } i ? View(i, types.Int32, address) : new ConstantValue((ulong)location.ConstantIndex, types.Int32, 32);
                    var element = array.Type is ArrayRef a ? a.Element : location.Type;
                    ManagedValue value = new ArrayElementValue(array, index, element, Width(element));
                    return path.Count == 0 ? value : Nest(store ? new AddressValue(value) : value, path, location.Type, store);
                }
            case LocationKind.Length:
                return new ArrayLengthValue(View(location.Base!, oracle.TypeOf(location.Base!), address), types.Int32, 32);
            case LocationKind.Local:
                {
                    var local = CellLocal((LocalSym)location.Base!);
                    return path.Count == 0 ? local : Nest(store ? new AddressValue(local) : local, path, location.Type, store);
                }
        }
        return Hole(address, $"内存 位置 {location.Kind} 尚未接入", location.Type);
    }

    private TypeRef FieldType(FieldRef field, TypeRef? leaf) => leaf ?? field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);

    private ManagedValue Nest(ManagedValue receiver, IReadOnlyList<FieldRef> path, TypeRef leaf, bool store = false)
    {
        var value = receiver;
        for (var i = 0; i < path.Count; i++)
        {
            var last = i == path.Count - 1;
            var type = FieldType(path[i], last ? leaf : null);
            value = new FieldValue(value, path[i], type, Width(type));
            if (store && !last && types.Kind(type) == TypeKind.Struct) value = new AddressValue(value);
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
            case LocalSym local when analysis.Memory.Find(local.Space, local.Offset, 1) is { Promoted: false } && oracle.Locate(local, 8) is { } place:
                return new AddressValue(LocationValue(place, address));
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
            case OperatorKind.Compare when op.Op.Cond is Cond.Eq or Cond.Ne && ClassIdentity(op.Args[0], op.Args[1]) is var (owner, sealedType):
                {
                    // 对象的类指针与密封类比较：等价于对象是否为该类型（读取类指针蕴含对象非空）。
                    var instance = new IsInstValue(View(owner, types.Object, address), sealedType);
                    return new ComparisonValue(op.Op.Cond == Cond.Eq ? Cond.Ne : Cond.Eq, instance, new ConstantValue(0, types.Object, 64), types.Boolean);
                }
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

    private (Sym Owner, TypeRef Type)? ClassIdentity(Sym left, Sym right)
    {
        foreach (var (a, b) in new[] { (left, right), (right, left) })
            if (ClassOwner(a) is { } owner && SymTable.Resolve(b) is EntitySym { Symbol: { Kind: SymbolKind.Class, Value: DefinitionRef type } }
                && (type.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) != 0)
                return (owner, type);
        return null;
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
            case TypeKind.Int or TypeKind.Pointer:
                {
                    var target = expected is not null && types.Kind(expected) is TypeKind.Int or TypeKind.Bool && Width(expected) >= slice.Width ? expected
                        : slice.Width is 8 or 16 or 32 or 64 ? types.Integer(slice.Width, false) : baseType;
                    if (target.Equals(types.Boolean) || slice.Width == 1 && types.Kind(target) == TypeKind.Bool)
                        return new ComparisonValue(Cond.Ne, IntegerBits(slice, baseType, address) ?? Hole(address, "值 位", baseType), new ConstantValue(0, baseType, Width(baseType)), types.Boolean);
                    return IntegerBits(slice, target, address) ?? Hole(address, $"值 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
                }
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
                    // bool 的零扩展即自身（C++ bool 只用低位）。
                    if (parts.Skip(1).All(p => p is ConstSym { Value: 0 } or UndefSym) && oracle.TypeOf(low) is { } lowType && types.Kind(lowType) == TypeKind.Bool)
                        return View(low, expected, address);
                    if (Width(expected) > 64 || Width(expected) < concat.Width && parts.Skip(1).Any(p => p is not (ConstSym { Value: 0 } or UndefSym))) break;
                    // 位组合的一般形式：各段零扩展后左移到其位置再按位或。未定义的位不参与。
                    ManagedValue? result = null;
                    var at = 0;
                    foreach (var part in parts)
                    {
                        var bit = at;
                        at += part.Width;
                        if (part is ConstSym { Value: 0 } or UndefSym || bit >= Width(expected)) continue;
                        if (IntegerBits(part, expected, address) is not { } bits) return Hole(address, $"值 拼接段 {part} 作为 {expected}", expected);
                        if (bit > 0) bits = new BinaryValue(BinOp.Shl, bits, new ConstantValue((ulong)bit, types.Int32, 32), expected, Width(expected));
                        result = result is null ? bits : new BinaryValue(BinOp.Or, result, bits, expected, Width(expected));
                    }
                    return result ?? new ConstantValue(0, expected, Width(expected));
                }
        }
        return Hole(address, $"值 拼接 {concat} 作为 {expected}", expected);
    }

    /// <summary>
    /// 一段位作为整数类型 target 的值（零扩展）：常量；整数原子；整数原子的切片为右移与掩码。
    /// 运算在来源的类型中进行，最后按宽度转换到 target。不能表达时为 null。
    /// </summary>
    private ManagedValue? IntegerBits(Sym part, TypeRef target, ulong address)
    {
        part = SymTable.Resolve(part);
        var targetWidth = Width(target);
        switch (part)
        {
            case ConstSym c:
                return new ConstantValue(c.Value & Expr.Mask(targetWidth), target, targetWidth);
            case SliceSym slice when oracle.TypeOf(slice.Base) is { } sourceType && types.Kind(sourceType) is TypeKind.Int or TypeKind.Pointer or TypeKind.Bool:
                {
                    var sourceWidth = Width(sourceType);
                    var value = View(slice.Base, sourceType, address);
                    if (slice.Low > 0) value = new BinaryValue(BinOp.LShr, value, new ConstantValue((ulong)slice.Low, types.Int32, 32), sourceType, sourceWidth);
                    if (slice.Width < sourceWidth && slice.Low + slice.Width < sourceWidth)
                        value = new BinaryValue(BinOp.And, value, new ConstantValue(Expr.Mask(slice.Width), sourceType, sourceWidth), sourceType, sourceWidth);
                    return Resize(value, target);
                }
            case not (SliceSym or ConcatSym) when oracle.TypeOf(part) is { } atomType && types.Kind(atomType) is TypeKind.Int or TypeKind.Bool or TypeKind.Pointer:
                return Resize(View(part, atomType, address), target);
        }
        return null;
    }

    /// <summary>整数值按宽度零扩展或截断到 target。</summary>
    private ManagedValue Resize(ManagedValue value, TypeRef target)
    {
        var (from, to) = (Width(value.Type), Width(target));
        if (from == to) return value.Type.Equals(target) ? value : Coerce(value, target);
        return new ConversionValue(from < to ? ConvKind.ZeroExtend : ConvKind.Truncate, value, target, to);
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
