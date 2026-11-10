using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

internal enum ReplacementKind
{
    /// <summary>区域换成对模板方法的调用。</summary>
    Call,
    /// <summary>待证构造：分配与区域换成 newobj。</summary>
    Construct,
    /// <summary>构造函数中缺少的基类构造：区域换成 base(...)。</summary>
    BaseConstructor,
}

/// <summary>一次替换的模板：方法、编好的模板方法体与替换的种类；构造时 Constructed 是新对象所在的局部。</summary>
internal sealed record Candidate(MethodRef Method, Program Template, ReplacementKind Kind, LocalValue? Constructed = null);

/// <summary>证明的入口：调用方在起点的状态（局部的值、共同的初始堆、路径条件、已初始化类型、实参）。</summary>
internal sealed class EntryState
{
    public required Term[] Arguments { get; init; }
    public required ImmutableList<Term> Phi { get; init; }
    public required ImmutableHashSet<TypeDef> Initialized { get; init; }
    public required Func<LocalValue, Term> Value { get; init; }
    public required Dictionary<Variable, Term> Evaluated { get; init; }
    public required SideState Heap { get; init; }
    /// <summary>可重算的表达式在入口状态下的值。</summary>
    public required Func<ManagedValue, Term?> Evaluate { get; init; }
}

/// <summary>
/// 区域的证明：以模板与调用方共同执行发现区域与出口（只提出候选），据此合成替换程序（调用前、调用、调用后、续接），
/// 再以复核（原方法体与展开调用后的新方法体共同执行）决定是否采纳。复核是采纳的唯一依据。
/// </summary>
internal sealed class RegionProver(ManagedTypes types, InlineEvidence evidence, Func<MethodRef, Program?> templates, Func<TypeRef, LocalValue> newLocal,
    Func<FieldRef, TypeRef, bool, TypeRef?, FieldAccessor?> accessor)
{
    public sealed record Outcome(ManagedBody? Body, string? Failure, int Progress, string Form)
    {
        /// <summary>这次尝试用掉的步数与各阶段耗时（诊断）。</summary>
        public long Steps { get; init; }
        public string Profile { get; init; } = "";
        /// <summary>各方案的结果（诊断）。</summary>
        public ImmutableList<string> Plans { get; init; } = [];
        /// <summary>失败与锚点无关：发现在模板返回前就失败，或从未按出口决定是否分叉。同一方法体上换锚点结果相同。</summary>
        public bool AnchorFree { get; init; }
    }

    /// <summary>值类型构造的证明：给定各叶子的值，解出构造函数与实参（9.2）。</summary>
    public Func<DefinitionRef, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>, ValueConstruction?>? ValueConstruction { get; init; }

    /// <summary>一次尝试的总步数上限。</summary>
    public const long AttemptSteps = 200_000;

    // ---- 入口 ----

    private static EntryState BuildEntry(Interpreter interpreter, Program caller, EntryFacts.State facts)
    {
        var terms = interpreter.Terms;
        var method = caller.Method;
        var definition = method.Method;
        var arguments = new Term[definition.Parameters.Count + 1];
        if (!definition.IsStatic)
        {
            var self = definition.Owner.IsValueType ? (TypeRef)new ByRefRef(method.DeclaringType) : method.DeclaringType;
            arguments[0] = interpreter.Atom(AtomKind.Argument, -1, self);
        }
        else arguments[0] = terms.Zero64;
        for (var i = 0; i < definition.Parameters.Count; i++)
            arguments[i + 1] = interpreter.Atom(AtomKind.Argument, i, method.Concrete(definition.Parameters[i].Type));
        var heap = new SideState { Frames = [] };
        var evaluated = new Dictionary<Variable, Term>();
        var active = new HashSet<Variable>();
        Term Local(LocalValue local)
        {
            if (evaluated.TryGetValue(local.Variable, out var known)) return known;
            Term value;
            if (caller.Cells.Contains(local.Variable))
                value = interpreter.ReadValue(heap, terms.CellRoot(0, local.Variable, FieldPath.Empty), local.Type, false) ?? interpreter.Atom(AtomKind.Entry, local.Variable, local.Type);
            else if (facts.Vars.TryGetValue(local.Variable, out var fact) && active.Add(local.Variable))
            {
                // 与解释器的局部同样按存储宽度保存（0/1 值存入 bool 局部时扩宽）。
                value = Evaluate(fact) is { } v ? interpreter.Stored(v, local.Type) : interpreter.Atom(AtomKind.Entry, local.Variable, local.Type);
                active.Remove(local.Variable);
            }
            else value = interpreter.Atom(AtomKind.Entry, local.Variable, local.Type);
            return evaluated[local.Variable] = value;
        }
        Term? Locate(ManagedValue value)
        {
            switch (value)
            {
                case FieldValue field when field.Receiver.Type is ByRefRef or PointerRef:
                    return Evaluate(field.Receiver) is { } address ? terms.ReferenceRoot(address, terms.Path([field.Field])) : null;
                case FieldValue field when ManagedTypes.IsReferenceType(field.Receiver.Type):
                    return Evaluate(field.Receiver) is { } obj ? terms.FieldRoot(obj, terms.Path([field.Field])) : null;
                case FieldValue field:
                    return Locate(field.Receiver) is { } inner && inner.Kind == TermKind.Location ? terms.Append(inner, terms.Path([field.Field])) : null;
                case StaticFieldValue field:
                    return terms.StaticRoot(terms.Path([field.Field]));
                case ArrayElementValue element:
                    return Evaluate(element.Array) is { } array && Evaluate(element.Index) is { } index ? terms.ElementRoot(array, index, FieldPath.Empty) : null;
                case IndirectValue indirect:
                    return Evaluate(indirect.Address) is { } target ? terms.ReferenceRoot(target, FieldPath.Empty) : null;
                case LocalValue local when caller.Cells.Contains(local.Variable):
                    return terms.CellRoot(0, local.Variable, FieldPath.Empty);
                default:
                    return null;
            }
        }
        Term? Evaluate(ManagedValue value)
        {
            Term? result;
            switch (value)
            {
                case LocalValue local:
                    return Local(local);
                case ArgumentValue argument:
                    return arguments[argument.Index + 1];
                case ConstantValue constant:
                    return interpreter.IsStruct(constant.Type) ? interpreter.Zero(constant.Type) : terms.Constant(constant.Bits, constant.Width);
                case StringValue text:
                    return terms.Atom(AtomKind.Text, text.Text, 64);
                case TypeHandleValue or SizeOfValue or FieldHandleValue or MethodHandleValue:
                    return terms.Atom(AtomKind.Token, value, value.Width);
                case FieldValue field when field.Receiver is LocalValue local && !caller.Cells.Contains(local.Variable) && interpreter.IsStruct(local.Type):
                    return interpreter.Project(Local(local), [field.Field], field.Type);
                case FieldValue or StaticFieldValue or ArrayElementValue or IndirectValue:
                    result = Locate(value) is { } location ? interpreter.ReadValue(heap, location, value.Type, false) : null;
                    break;
                case ArrayLengthValue length:
                    result = Evaluate(length.Array) is { } array ? terms.Read(0, terms.LengthRoot(array), 32, false) : null;
                    if (result is not null && length.Width != 32) result = terms.Convert(ConvKind.ZeroExtend, result, length.Width);
                    break;
                case StringLengthValue length:
                    result = Evaluate(length.String) is { } text2 ? terms.Read(0, terms.StringLengthRoot(text2), 32, false) : null;
                    break;
                case AddressValue address:
                    result = Locate(address.Target) is { } target ? terms.Address(target) : null;
                    break;
                case BinaryValue binary:
                    result = Evaluate(binary.Left) is { } l && Evaluate(binary.Right) is { } r ? terms.Binary(binary.Op, l, r, binary.Width) : null;
                    break;
                case UnaryValue unary:
                    result = Evaluate(unary.Operand) is { } u ? terms.Unary(unary.Op, u, unary.Width) : null;
                    break;
                case ConversionValue conversion:
                    result = Evaluate(conversion.Operand) is { } c ? terms.Convert(conversion.Kind, c, conversion.Width) : null;
                    break;
                case ComparisonValue comparison:
                    result = Evaluate(comparison.Left) is { } cl && Evaluate(comparison.Right) is { } cr ? terms.Compare(comparison.Condition, cl, cr) : null;
                    break;
                case BooleanValue boolean:
                    result = Evaluate(boolean.Left) is { } bl && Evaluate(boolean.Right) is { } br ? boolean.IsAnd ? terms.And(bl, br) : terms.Or(bl, br) : null;
                    break;
                case NegatedValue negated:
                    result = Evaluate(negated.Operand) is { } n ? terms.Not(n) : null;
                    break;
                case ChoiceValue choice:
                    result = Evaluate(choice.Condition) is { } cc && Evaluate(choice.True) is { } ct && Evaluate(choice.False) is { } cf
                        ? terms.Choice(cc, ct, cf, choice.Width) : null;
                    break;
                case IsInstValue isinst:
                    result = Evaluate(isinst.Operand) is { } o ? terms.Operation(OpCode.IsInst, 0, 64, isinst.Target, o) : null;
                    break;
                default:
                    return null;
            }
            if (result is not null) result.Hint ??= value.Type;
            return result;
        }
        void Know(Term location, Term value, TypeRef type)
        {
            if (value.Kind == TermKind.Tuple && interpreter.IsStruct(type))
            {
                var leaves = interpreter.Leaves(type);
                if (leaves.Length == value.Args.Length)
                    for (var i = 0; i < leaves.Length; i++)
                        terms.Know(leaves[i].Path.Count == 0 ? location : terms.Append(location, leaves[i].Path), value.Args[i]);
                return;
            }
            if (value.Kind != TermKind.Tuple) terms.Know(location, value);
        }
        // 入口知识：按定义已知内容的结构体单元，与已知的存储内容。
        foreach (var (variable, fact) in facts.Vars)
            if (caller.Cells.Contains(variable) && caller.LocalOf(variable) is { } cell && active.Add(variable))
            {
                if (Evaluate(fact) is { } content) Know(terms.CellRoot(0, variable, FieldPath.Empty), content, cell.Type);
                active.Remove(variable);
            }
        foreach (var (location, content) in facts.Known)
            if (Locate(location) is { } at && Evaluate(content) is { } v) Know(at, v, location.Type);
        var phi = ImmutableList<Term>.Empty;
        if (!definition.IsStatic && !definition.Owner.IsValueType)
            phi = phi.Add(terms.Not(terms.Compare(Cond.Eq, arguments[0], terms.Zero64)));
        foreach (var (condition, holds) in facts.Literals)
            if (Evaluate(condition) is { } c && !c.IsConstant) phi = phi.Add(holds ? terms.ToBit(c) : terms.Not(c));
        foreach (var variable in facts.NonNull)
            if (caller.LocalOf(variable) is { } local && ManagedTypes.IsReferenceType(local.Type) && Local(local) is { Width: 64 } v)
                phi = phi.Add(terms.Not(terms.Compare(Cond.Eq, v, terms.Zero64)));
        phi = ImmutableList.CreateRange(phi.Where(l => !l.IsConstant).Distinct(ReferenceEqualityComparer.Instance).Cast<Term>());
        return new EntryState
        {
            Arguments = arguments, Phi = phi, Initialized = facts.Initialized.ToImmutableHashSet(), Value = Local,
            Evaluated = evaluated, Heap = heap, Evaluate = Evaluate,
        };
    }

    /// <summary>程序点上局部的值与某个表达式此刻的值是否为同一个项（入口状态的性质，供模型检查）。</summary>
    internal static bool SameAtEntry(ManagedTypes types, InlineEvidence evidence, ManagedBody body, ulong block, int index, LocalValue local, ManagedValue value)
    {
        var program = Program.Compile(body, types);
        var interpreter = new Interpreter(types, new Solver(new TermTable(), types), evidence);
        var entry = BuildEntry(interpreter, program, new EntryFacts(program).At(block, index));
        return entry.Evaluate(value) is { } expected && ReferenceEquals(entry.Value(local), expected);
    }

    // ---- 发现 ----

    private sealed class Attempt
    {
        public required TermTable Terms { get; init; }
        public required Solver Solver { get; init; }
        public required Interpreter Interpreter { get; init; }
        public required EntryState Entry { get; init; }
        public required Program Caller { get; init; }
        public required ulong Block { get; init; }
        public required int Index { get; init; }
        public required Candidate Candidate { get; init; }
        /// <summary>模板的形参（下标 0 为 this）。</summary>
        public Term[] Formals { get; set; } = [];
        /// <summary>区域必须覆盖的语句（待证访问、待证构造的基类构造调用）；出口语句满足时须改写。</summary>
        public required Func<TracePoint, bool> Anchor { get; init; }
    }

    private static int FirstOp(Program program, ulong block, int index)
    {
        var ops = program.Units[program.BlockUnits[block]].Ops;
        for (var i = 0; i < ops.Length; i++)
            if (ops[i].Statement >= index) return i;
        return ops.Length;
    }

    private static bool HasPending(ManagedStatement statement) => ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement))
        .SelectMany(ManagedValues.Walk).Any(v => v is FieldValue { Pending: not null } or StaticFieldValue { Pending: not null });

    private SideState CallerSide(Attempt attempt, Program program, bool tracing)
    {
        var frame = new Frame
        {
            Program = program, Id = 0, Unit = program.BlockUnits[attempt.Block], Op = FirstOp(program, attempt.Block, attempt.Index),
            Arguments = attempt.Entry.Arguments, Temps = new Term[Math.Max(1, program.Temps)],
        };
        var side = new SideState
        {
            Frames = [frame], Initialized = attempt.Entry.Initialized, Entry = attempt.Entry.Value,
            Tracing = tracing, PendingAt = tracing ? (b, i) => HasPending(program.Blocks[b].Statements[i]) : null,
        };
        if (attempt.Candidate is { Kind: ReplacementKind.Construct, Constructed: { } local })
        {
            side.AllocationTarget = local;
            side.Stop = new Stop(StopKind.Event) { Event = new EventInfo(EventKind.Allocate, local.Type, null, [], false) { ResultType = local.Type } };
        }
        return side;
    }

    private SideState TemplateSide(Attempt attempt)
    {
        var interpreter = attempt.Interpreter;
        var method = attempt.Candidate.Method;
        var definition = method.Method;
        var formals = new Term[definition.Parameters.Count + 1];
        formals[0] = attempt.Terms.Zero64;
        if (!definition.IsStatic && attempt.Candidate.Kind == ReplacementKind.Call)
            formals[0] = interpreter.Atom(AtomKind.Formal, -1, definition.Owner.IsValueType ? new ByRefRef(method.DeclaringType) : method.DeclaringType);
        if (attempt.Candidate.Kind == ReplacementKind.BaseConstructor) formals[0] = attempt.Entry.Arguments[0];
        for (var i = 0; i < definition.Parameters.Count; i++)
            formals[i + 1] = interpreter.Atom(AtomKind.Formal, i, method.Concrete(definition.Parameters[i].Type));
        attempt.Formals = formals;
        var program = attempt.Candidate.Template;
        // 调用点的异常上下文：模板中的抛出都从调用处传出。
        var region = attempt.Caller.HandlerOf(attempt.Block);
        var live = new Dictionary<Variable, Term>();
        var side = new SideState
        {
            Frames = [], Initialized = attempt.Entry.Initialized,
            OuterContext = (region?.HandlerEntry, live),
        };
        var evt = new EventInfo(attempt.Candidate.Kind == ReplacementKind.Construct ? EventKind.Construct : EventKind.Call, method,
            definition.IsStatic || attempt.Candidate.Kind == ReplacementKind.Construct ? null : formals[0], formals.Skip(1).ToArray(), false);
        if (attempt.Candidate.Kind == ReplacementKind.Construct) interpreter.BeginConstruct(side, program, evt);
        else
        {
            interpreter.Unfold(side, program, evt, null);
            // callvirt 先对接收者判空。
            if (!definition.IsStatic && !definition.Owner.IsValueType && attempt.Candidate.Kind == ReplacementKind.Call) side.EntryCheck = formals[0];
        }
        return side;
    }

    /// <summary>发现：模板与调用方共同执行；有路径因绑定太晚或形参被常量折叠而失败时，带着绑定与缩窄重试。</summary>
    private List<PathOutcome>? Discover(Attempt attempt, out string? failure) => Discover(attempt, out failure, out _);

    private List<PathOutcome>? Discover(Attempt attempt, out string? failure, out bool anchored)
    {
        anchored = false;
        var seed = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        // 模板中在调用方被内联的调用点：路径因等待而失败、模板停在可展开的事件上时，下一轮在那里立即展开。
        var eager = new HashSet<(Program, int, int)>();
        List<PathOutcome>? outcomes = null;
        failure = null;
        for (var round = 0; round < 6; round++)
        {
            attempt.Solver.Reset(seed);
            attempt.Solver.Allocations.Clear();
            var path = new JointPath { A = TemplateSide(attempt), B = CallerSide(attempt, attempt.Caller, true), Phi = attempt.Entry.Phi };
            string? unsettled = null;
            var joint = new Joint(attempt.Interpreter, templates, JointMode.Discovery)
            {
                Settled = p => Exits(attempt, new PathOutcome(p, null), out unsettled, true).Count > 0,
                Eager = new HashSet<(Program, int, int)>(eager),
                Formals = attempt.Formals,
            };
            // 第一条失败路径就足以推出缩窄；其余路径在重试中再走。
            outcomes = joint.Run(path, true);
            if (unsettled is not null)
                outcomes = outcomes.Select(o => o.Failure is { } f && f.StartsWith("联合路径超过预算", StringComparison.Ordinal) ? o with { Failure = $"{f}（模板返回时没有出口：{unsettled}）" } : o).ToList();
            anchored |= joint.ConsultedSettled;
            var failed = outcomes.Where(o => !o.Success).ToArray();
            // 发现后的绑定下不可行的路径不存在（较早的路径在绑定确定之前走过），不参与出口。
            if (failed.Length == 0) return outcomes.Where(o => !o.Vacuous && !attempt.Solver.Infeasible(o.Path.Phi)).ToList();
            failure = failed[0].Failure;
            // 换成展开的假设后重来：这一轮的绑定建立在另一种假设上，不沿用。
            if (failed.Where(o => o.Path.Stalled).Select(o => o.Path.Waiting).OfType<(Program, int, int)>().Count(eager.Add) > 0) continue;
            var next = attempt.Solver.Snapshot();
            foreach (var (formal, value) in Narrowing(attempt, failed)) next.TryAdd(formal, value);
            if (next.Count == seed.Count) return null;
            seed = next;
        }
        return null;
    }

    /// <summary>形参的缩窄：失败路径的条件里只含未绑定形参的文字，取使它不成立的常量。</summary>
    private static IEnumerable<KeyValuePair<Term, Term>> Narrowing(Attempt attempt, PathOutcome[] failed)
    {
        var terms = attempt.Terms;
        foreach (var outcome in failed)
            foreach (var raw in outcome.Path.Phi)
            {
                var literal = attempt.Solver.Apply(raw);
                if (!literal.HasFormal) continue;
                var negated = literal.IsOp(OpCode.Not);
                var atom = negated ? literal.Args[0] : literal;
                if (atom.IsOp(OpCode.ToBit) && atom.Args[0].IsAtom(AtomKind.Formal))
                    yield return new(atom.Args[0], terms.Constant(negated ? 1UL : 0UL, atom.Args[0].Width));
                else if (atom.IsAtom(AtomKind.Formal) && atom.Width == 1)
                    yield return new(atom, terms.Constant(negated ? 1UL : 0UL, 1));
                else if (atom.IsOp(OpCode.Compare) && atom.Cond == Cond.Eq && atom.Args[0].IsAtom(AtomKind.Formal) && atom.Args[1].IsConstant)
                {
                    // 失败路径假设 F == k：取另一个值只对布尔有意义；假设 F != k（negated）：取 k。
                    if (negated) yield return new(atom.Args[0], atom.Args[1]);
                    else if (atom.Args[0].Bit) yield return new(atom.Args[0], terms.Constant(atom.Args[1].Bits == 0 ? 1UL : 0UL, atom.Args[0].Width));
                }
            }
    }

    // ---- 出口 ----

    /// <summary>一条返回路径的出口：调用方轨迹中的语句位置。</summary>
    /// <summary>路径上的出口；Covered 为区域覆盖的待证访问数（出口语句是可改写的待证读取时算上它）。</summary>
    private sealed record Exit(PathOutcome Path, int Trace, TracePoint Point, Term? Returned)
    {
        public int Covered { get; init; }
    }

    private static SideState Snapshot(TracePoint point) => new()
    {
        Frames = [], Writes = point.Writes, Version = point.Version, Exposed = point.Exposed, Fresh = point.Fresh,
    };

    /// <summary>
    /// 路径上的出口（按轨迹顺序）：调用方完成模板的全部事件、模板的公共写入都已出现、（经过锚点的路径）覆盖锚点的轨迹点。
    /// 出口语句是待证读取时它被改写（5.5），出口可以就在这里；待证写入不能改写，出口要么在它之前（它留在续接里）、要么在它之后。
    /// strict 时写入必须在已提交的绑定下相同（共同执行中途判断是否已到出口，未绑定的形参不能当场试探成任意值）。
    /// </summary>
    private static List<Exit> Exits(Attempt attempt, PathOutcome outcome, out string? failure, bool strict = false)
    {
        var template = outcome.Path.A;
        var caller = outcome.Path.B;
        var interpreter = attempt.Interpreter;
        var exits = new List<Exit>();
        var writes = template.Writes.Where(w => !TermTable.Immutable(w.Location) && !interpreter.Private(template, w.Location)).ToArray();
        // 经过锚点的路径，出口在锚点之后（区域要覆盖待证访问）；不经过锚点的路径不受此约束，进展由整个替换判定。
        var covered = !caller.Trace.Any(attempt.Anchor);
        var passed = 0;
        failure = null;
        string? missing = null;
        var reached = false;
        for (var j = 0; j < caller.Trace.Count; j++)
        {
            var point = caller.Trace[j];
            if (point.Events == template.Events)
            {
                reached = true;
                var snapshot = Snapshot(point);
                var phi = outcome.Path.Phi;
                var differs = writes.FirstOrDefault(w =>
                {
                    var location = attempt.Solver.Fold(phi, w.Location);
                    if (strict && location.HasFormal) return true;
                    var actual = interpreter.ReadScalar(snapshot, location, new Leaf(FieldPath.Empty, HintOf(w.Value), w.Value.Width, w.Value.Bit), false);
                    var trial = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
                    return actual is null || !attempt.Solver.MatchUnder(phi, w.Value, actual, trial) || strict && trial.Count > 0;
                });
                if (differs.Location is not null)
                {
                    var location = attempt.Solver.Fold(phi, differs.Location);
                    var actual = interpreter.ReadScalar(snapshot, location, new Leaf(FieldPath.Empty, HintOf(differs.Value), differs.Value.Width, differs.Value.Bit), false);
                    // 不可判定时给出挡住读取的写入。
                    var blocking = actual is null ? snapshot.Writes.LastOrDefault(w => !ReferenceEquals(w.Location, location) && interpreter.MayOverlap(snapshot, w.Location, location)).Location : null;
                    missing = $"模板写入 {location} = {attempt.Solver.Fold(phi, differs.Value)} 在调用方 {point.Block:x}:{point.Statement} 处没有出现（调用方此处为 {(actual is null ? $"不可判定，可能重叠的写入 {blocking}" : attempt.Solver.Fold(phi, actual))}）";
                }
                // 中途判断（strict）只认已覆盖之后的出口：停在待证读取上的出口要靠改写才有用，不能用来截断区域。
                else
                {
                    var rewritten = point.Pending && PendingRead(attempt.Caller.Blocks[point.Block].Statements[point.Statement]);
                    if (covered || rewritten && !strict) exits.Add(new Exit(outcome, j, point, template.Stop?.Value) { Covered = passed + (rewritten ? 1 : 0) });
                }
            }
            covered |= attempt.Anchor(point);
            if (point.Pending) passed++;
        }
        if (exits.Count > 0) return exits;
        failure = !reached ? $"调用方没有完成模板的 {template.Events} 个事件（轨迹 {caller.Trace.Count} 个语句）"
            : missing ?? "区域不含待证访问";
        return exits;

        static TypeRef HintOf(Term t) => t.Hint ?? new PrimitiveRef("int");
    }

    private static bool PendingRead(ManagedStatement statement) => ManagedValues.Of(statement).SelectMany(ManagedValues.Walk)
        .Any(v => v is FieldValue { Pending.Write: false } or StaticFieldValue { Pending.Write: false });

    // ---- 写回 ----

    /// <summary>写回的时刻：调用前（入口状态）或调用后（模板在这条路径上的最终状态与返回值）。</summary>
    private sealed record Moment
    {
        public required SideState Heap { get; init; }
        public Term? Result { get; init; }
        public LocalValue? ResultLocal { get; init; }
        /// <summary>此刻持有某个值的局部。</summary>
        public required Dictionary<Term, ManagedValue> Locals { get; init; }
        /// <summary>可以写在调用之前的语句（只在调用前的时刻有）：值的写法需要先有语句时（对象初始化器）加在这里。</summary>
        public List<ManagedStatement>? Prelude { get; init; }
        /// <summary>调用前语句的地址。</summary>
        public ulong At { get; init; }
    }

    private TypeRef FieldType(FieldRef field) => field.DeclaringType is DefinitionRef owner ? field.Field.Type.Substitute(owner.Arguments, []) : field.Field.Type;

    private ManagedValue? Reify(Attempt attempt, Moment moment, Term term, TypeRef? want)
    {
        var terms = attempt.Terms;
        // 常量写成常量本身：返回常量的路径上同值的常量不一定是返回值（各路径的写法由 Expression 合并）。
        if (moment.Result is { } result && moment.ResultLocal is { } resultLocal && !term.IsConstant)
        {
            if (ReferenceEquals(term, result)) return resultLocal;
            // 0/1 值：等于返回值或其取反（规范形下取反是同一个项的否定）。
            if (term.Bit && result.Bit && result.Kind != TermKind.Tuple)
            {
                var bit = terms.ToBit(result);
                if (ReferenceEquals(term, bit)) return resultLocal;
                if (ReferenceEquals(terms.Not(term), bit)) return new NegatedValue(resultLocal, types.Boolean);
            }
            // 窄值：返回值的低位（返回值是它的扩展，截断后就是它）。
            if (result.Kind != TermKind.Tuple && term.Width is 8 or 16 or 32 && term.Width < result.Width && ReferenceEquals(terms.Convert(ConvKind.Truncate, result, term.Width), term))
                return new ConversionValue(ConvKind.Truncate, resultLocal, want ?? term.Hint ?? types.Integer(term.Width, false), term.Width);
            if (result.Kind == TermKind.Tuple && result.Key is DefinitionRef structure)
            {
                var leaves = attempt.Interpreter.Leaves(structure);
                for (var i = 0; i < leaves.Length; i++)
                    if (ReferenceEquals(result.Args[i], term) && leaves[i].Path.Count > 0 && Chain(resultLocal, leaves[i].Path.Fields) is { } field) return field;
                // 窄值：返回值某个字段的低位。
                for (var i = 0; i < leaves.Length; i++)
                    if (leaves[i].Path.Count > 0 && term.Width is 8 or 16 or 32 && term.Width < result.Args[i].Width
                        && ReferenceEquals(terms.Convert(ConvKind.Truncate, result.Args[i], term.Width), term) && Chain(resultLocal, leaves[i].Path.Fields) is { } field)
                        return new ConversionValue(ConvKind.Truncate, field, want ?? term.Hint ?? types.Integer(term.Width, false), term.Width);
            }
        }
        // 实参在整个方法中不变，直接写成实参（结构体实参是它的叶子元组）。
        if (term.IsAtom(AtomKind.Argument) && Argument(attempt, term) is { } argument) return argument;
        if (term.Kind == TermKind.Tuple)
            for (var i = 1; i < attempt.Entry.Arguments.Length; i++)
                if (ReferenceEquals(attempt.Entry.Arguments[i], term)) return ArgumentRoot(attempt, i - 1);
        if (moment.Locals.TryGetValue(term, out var held)) return held;
        switch (term.Kind)
        {
            case TermKind.Constant:
                {
                    var type = want ?? term.Hint ?? (term.Width == 1 ? types.Boolean : types.Integer(term.Width <= 32 ? 32 : 64, true));
                    // 结构体类型的零值（类型形参按约束是结构体时它是一个标量项）写成 default。
                    if (attempt.Interpreter.IsStruct(type)) return ReferenceEquals(term, attempt.Interpreter.Zero(type)) ? new ComposedValue(type, []) : null;
                    return new ConstantValue(term.Bits, type, term.Width);
                }
            case TermKind.Atom:
                return term.Atom switch
                {
                    AtomKind.Entry => EntryLocal(attempt, term),
                    AtomKind.Argument => Argument(attempt, term),
                    AtomKind.Text => new StringValue((string)term.Key!, types.String),
                    AtomKind.Token => term.Key as ManagedValue,
                    _ => null,
                };
            case TermKind.Read:
                {
                    var leaf = new Leaf(FieldPath.Empty, term.Hint ?? types.Int32, term.Width, term.Bit);
                    var reread = attempt.Interpreter.ReadScalar(moment.Heap, term.Location, leaf, false);
                    if (ReferenceEquals(reread, term)) return Location(attempt, moment, term.Location);
                    if (reread is not null) reread = attempt.Solver.Apply(reread);
                    // 此刻的内容是原内容加或异或一个常量：原内容由此刻的读取反解。
                    if (reread is { Kind: TermKind.Operation, Op: OpCode.Binary, BinOp: BinOp.Add or BinOp.Xor } && reread.Args[1].IsConstant
                        && ReferenceEquals(reread.Args[0], term) && Location(attempt, moment, term.Location) is { } now)
                    {
                        var k = reread.Args[1].Bits & TermTable.Mask(term.Width);
                        var negated = (0 - k) & TermTable.Mask(term.Width);
                        var (op, constant) = reread.BinOp == BinOp.Xor ? (BinOp.Xor, k) : negated <= k ? (BinOp.Add, negated) : (BinOp.Sub, k);
                        return new BinaryValue(op, now, new ConstantValue(constant, now.Type, term.Width), now.Type, term.Width);
                    }
                    return null;
                }
            case TermKind.Address:
                return Location(attempt, moment, term.Location, Use.Address) is { } target ? new AddressValue(target) : null;
            case TermKind.Tuple:
                return Composite(attempt, moment, term);
            case TermKind.Operation:
                return Operation(attempt, moment, term, want);
            default:
                return null;
        }
    }

    private ManagedValue? Operation(Attempt attempt, Moment moment, Term term, TypeRef? want)
    {
        ManagedValue? Sub(int i, TypeRef? type = null) => Reify(attempt, moment, term.Args[i], type);
        switch (term.Op)
        {
            case OpCode.Binary:
                {
                    if (Sub(0) is not { } l || Sub(1, l.Type) is not { } r) return null;
                    return new BinaryValue(term.BinOp, l, r, term.Hint ?? want ?? l.Type, term.Width);
                }
            case OpCode.Unary:
                return Sub(0) is { } u ? new UnaryValue((UnOp)term.Aux, u, term.Hint ?? want ?? u.Type, term.Width) : null;
            case OpCode.Convert:
                {
                    // 0/1 值按 bool 的存储宽度保存（局部、字段、返回值）：写成 bool 时就是这个值本身。
                    if (term.Conv == ConvKind.ZeroExtend && term.Args[0].Width == 1 && (want is null || want == types.Boolean)) return Sub(0, types.Boolean);
                    if (Sub(0) is not { } c) return null;
                    var type = term.Hint ?? want ?? (term.Width == 1 ? types.Boolean : types.Integer(term.Width <= 32 ? 32 : 64, term.Conv == ConvKind.SignExtend));
                    return new ConversionValue(term.Conv, c, type, term.Width);
                }
            case OpCode.Compare:
                {
                    if (Sub(0) is not { } l || Sub(1, l.Type) is not { } r) return null;
                    return new ComparisonValue(term.Cond, l, r, types.Boolean);
                }
            case OpCode.And:
            case OpCode.Or:
                return Sub(0) is { } a && Sub(1) is { } b ? new BooleanValue(term.Op == OpCode.And, a, b, types.Boolean) : null;
            case OpCode.Not:
                return Sub(0) is { } n ? new NegatedValue(n, types.Boolean) : null;
            case OpCode.ToBit:
                return Sub(0);
            case OpCode.Choice:
                {
                    if (Sub(0) is not { } c || Sub(1, want) is not { } t || Sub(2, t.Type) is not { } f) return null;
                    return new ChoiceValue(c, t, f, t.Type, term.Width);
                }
            case OpCode.IsInst:
                return Sub(0) is { } o ? new IsInstValue(o, (TypeRef)term.Key!) : null;
            default:
                return null;
        }
    }

    private ManagedValue? Composite(Attempt attempt, Moment moment, Term tuple)
    {
        var structure = (DefinitionRef)tuple.Key!;
        var leaves = attempt.Interpreter.Leaves(structure);
        // 同一位置的全部叶子：整体读取。
        if (tuple.Args.All(a => a.Kind == TermKind.Read) && leaves.Length == tuple.Args.Length)
        {
            var first = tuple.Args[0].Location;
            var path = TermTable.PathOf(first);
            if (path.Count >= leaves[0].Path.Count)
            {
                var root = attempt.Terms.Truncate(first, path.Count - leaves[0].Path.Count);
                if (root is not null && tuple.Args.Select((a, i) => (a, i)).All(p => ReferenceEquals(p.a.Location, attempt.Terms.Append(root, leaves[p.i].Path))
                    && ReferenceEquals(attempt.Interpreter.ReadScalar(moment.Heap, p.a.Location, leaves[p.i], false), p.a)))
                    return Location(attempt, moment, root);
            }
        }
        // 同一局部的全部叶子。
        if (tuple.Args.All(a => a.IsAtom(AtomKind.Entry)) && tuple.Args[0].Key is TermTable.LeafKey { Root: Variable variable }
            && attempt.Caller.LocalOf(variable) is { } local && ReferenceEquals(attempt.Entry.Value(local), tuple))
            return local;
        // 逐叶子组成，缺的叶子为零。
        var parts = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        for (var i = 0; i < leaves.Length; i++)
        {
            if (tuple.Args[i].IsConstant && tuple.Args[i].Bits == 0) continue;
            if (leaves[i].Path.Count == 0 || Reify(attempt, moment, tuple.Args[i], leaves[i].Type) is not { } value) return null;
            parts.Add((leaves[i].Path.Fields, value));
        }
        return Compose(structure, parts, moment);
    }

    /// <summary>
    /// 结构体值的托管写法：字段都可访问时逐字段组成；否则以值类型构造的摘要证明 new S(args)（9.2）；叶子都是直接字段时写成对象初始化器；
    /// 再把内层结构体的叶子收拢成直接字段的值后重试。
    /// </summary>
    private ManagedValue? Compose(DefinitionRef structure, List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> parts, Moment moment)
    {
        if (parts.All(p => p.Path.All(f => evidence.Accessible(f, f.DeclaringType)))) return new ComposedValue(structure, parts);
        if (ValueConstruction?.Invoke(structure, parts) is { } construction) return new NewObjectValue(construction.Constructor, construction.Arguments) { Transparent = true };
        if (parts.All(p => p.Path.Count == 1)) return Initializer(structure, parts, moment);
        var direct = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        foreach (var group in parts.GroupBy(p => p.Path[0]))
        {
            if (group.Count() == 1 && group.First().Path.Count == 1) { direct.Add(group.First()); continue; }
            if (FieldType(group.Key) is not DefinitionRef nested
                || Compose(nested, group.Select(p => ((IReadOnlyList<FieldRef>)p.Path.Skip(1).ToArray(), p.Value)).ToList(), moment) is not { } whole) return null;
            direct.Add(([group.Key], whole));
        }
        return Compose(structure, direct, moment);
    }

    /// <summary>
    /// 对象初始化器 new S { A = a, B = b }：initobj 之后逐个写字段，不可访问的字段经证明过的 setter。setter 内联后只留下字段写入，
    /// 所以与按叶子组成等价。需要先有语句，只在调用之前的时刻可用：语句加到 Prelude，值是写好的局部。
    /// </summary>
    private ManagedValue? Initializer(DefinitionRef structure, List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> parts, Moment moment)
    {
        if (moment.Prelude is not { } prelude) return null;
        var receiver = new ByRefRef(structure);
        if (parts.Any(p => (p.Path[0].Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            || !evidence.Accessible(p.Path[0], receiver) && accessor(p.Path[0], FieldType(p.Path[0]), true, receiver) is null)) return null;
        var copy = newLocal(structure);
        var statements = new List<ManagedStatement> { new ManagedAssignment(moment.At, copy, new ComposedValue(structure, [])) };
        foreach (var (path, value) in parts)
        {
            if (Step(new AddressValue(copy), path[0], true, Use.Write) is not { } place) return null;
            statements.Add(new ManagedStore(moment.At, place, value));
        }
        prelude.AddRange(statements);
        return copy;
    }

    /// <summary>值的字段链（读取）：每一层都要对调用方可访问或经已证明的 getter，否则写不出。</summary>
    private ManagedValue? Chain(ManagedValue root, IReadOnlyList<FieldRef> path)
    {
        for (var i = 0; i < path.Count; i++)
        {
            if (Step(root, path[i], i == path.Count - 1, Use.Read) is not { } next) return null;
            root = next;
        }
        return root;
    }

    private ManagedValue? EntryLocal(Attempt attempt, Term atom)
    {
        var (variable, pathId) = atom.Key switch { Variable v => (v, 0), TermTable.LeafKey { Root: Variable v } p => (v, p.Path), _ => (null!, -1) };
        if (pathId < 0 || attempt.Caller.LocalOf(variable) is not { } local) return null;
        if (pathId == 0) return local;
        var leaf = attempt.Interpreter.Leaves(local.Type).FirstOrDefault(l => l.Path.Id == pathId);
        return leaf is null ? null : Chain(local, leaf.Path.Fields);
    }

    private ManagedValue? Argument(Attempt attempt, Term atom)
    {
        var (index, pathId) = atom.Key switch { int i => (i, 0), TermTable.LeafKey { Root: int i } p => (i, p.Path), _ => (int.MinValue, -1) };
        if (pathId < 0) return null;
        var argument = ArgumentRoot(attempt, index);
        if (pathId == 0) return argument;
        var leaf = attempt.Interpreter.Leaves(argument.Type).FirstOrDefault(l => l.Path.Id == pathId);
        return leaf is null ? null : Chain(argument, leaf.Path.Fields);
    }

    private ArgumentValue ArgumentRoot(Attempt attempt, int index)
    {
        var method = attempt.Caller.Method;
        var type = index < 0 ? method.Method.Owner.IsValueType ? new ByRefRef(method.DeclaringType) : method.DeclaringType
            : method.Concrete(method.Method.Parameters[index].Type);
        return new ArgumentValue(index, type, types.ValueWidth(type));
    }

    /// <summary>位置写成托管的位置表达式（字段、静态字段、元素、经引用、局部）；不可访问的字段不能写回。</summary>
    private enum Use { Read, Write, Address }

    private ManagedValue? Location(Attempt attempt, Moment moment, Term location, Use use = Use.Read)
    {
        var path = TermTable.PathOf(location).Fields;
        ManagedValue? root;
        int skip;
        switch (location.Root)
        {
            case RootKind.Field:
                {
                    if (Reify(attempt, moment, location.Args[0], null) is not { } obj || path.Length == 0) return null;
                    root = obj;
                    skip = 0;
                    break;
                }
            case RootKind.Static:
                {
                    if (path.Length == 0) return null;
                    root = Step(null, path[0], path.Length == 1, use);
                    skip = 1;
                    break;
                }
            case RootKind.Element:
                {
                    if (Reify(attempt, moment, location.Args[0], null) is not { Type: ArrayRef array } arr
                        || Reify(attempt, moment, location.Args[1], types.Int32) is not { } index) return null;
                    root = new ArrayElementValue(arr, index, array.Element, types.ValueWidth(array.Element));
                    skip = 0;
                    break;
                }
            case RootKind.Reference:
                {
                    if (Reify(attempt, moment, location.Args[0], null) is not { Type: ByRefRef reference } address) return null;
                    if (path.Length == 0) return new IndirectValue(address, reference.Element, types.ValueWidth(reference.Element));
                    root = address;
                    skip = 0;
                    break;
                }
            case RootKind.Cell when location.Aux == 0:
                {
                    if (attempt.Caller.LocalOf(TermTable.CellVariable(location)) is not { } local) return null;
                    root = local;
                    skip = 0;
                    break;
                }
            case RootKind.Length:
                return Reify(attempt, moment, location.Args[0], null) is { } a ? new ArrayLengthValue(a, types.Int32, 32) : null;
            case RootKind.StringLength:
                return Reify(attempt, moment, location.Args[0], null) is { } s ? new StringLengthValue(s, types.Int32) : null;
            default:
                return null;
        }
        for (var i = skip; i < path.Length && root is not null; i++) root = Step(root, path[i], i == path.Length - 1, use);
        return root;
    }

    /// <summary>
    /// 访问一层字段。不可访问的字段经已证明的访问器：读取时每一层都可以经 getter（结构体值按复制取下去）；
    /// 写入只有最后一层可以经 setter；取地址不能经过访问器。
    /// </summary>
    private ManagedValue? Step(ManagedValue? receiver, FieldRef field, bool last, Use use)
    {
        // 路径中的字段可能取自共享实例（引用类型实参为 object）：按接收者的静态类型还原声明类型。
        if ((receiver?.Type is ByRefRef byRef ? byRef.Element : receiver?.Type) is DefinitionRef owner && field.DeclaringType is DefinitionRef declared
            && ReferenceEquals(owner.Definition, declared.Definition) && !owner.Equals(declared))
            field = field with { DeclaringType = owner };
        var type = FieldType(field);
        var width = types.ValueWidth(type);
        ManagedValue access = receiver is null ? new StaticFieldValue(field, type, width) : new FieldValue(receiver, field, type, width);
        if (evidence.Accessible(field, receiver?.Type)) return access;
        var write = use == Use.Write && last;
        if (use == Use.Address || use == Use.Write && !last || accessor(field, type, write, receiver?.Type) is not { } proven) return null;
        return access switch
        {
            FieldValue f => f with { Accessor = proven },
            StaticFieldValue f => f with { Accessor = proven },
            _ => null,
        };
    }

    // ---- 合成与复核 ----

    /// <summary>
    /// 证明一次替换：发现、选出口、合成替换程序、复核。progress 是失败时比较走得多远（覆盖的调用方语句数），用于挑选诊断。
    /// </summary>
    /// <param name="useful">替换是否有进展（覆盖了要证的内容）；没有进展的替换不算成立，继续试其他出口与方案。</param>
    public Outcome Prove(Program caller, EntryFacts facts, ulong block, int index, Candidate candidate, Func<TracePoint, bool> anchor, Func<ManagedBody, bool>? useful = null)
    {
        var terms = new TermTable();
        var solver = new Solver(terms, types);
        var meter = new Meter(AttemptSteps);
        var interpreter = new Interpreter(types, solver, evidence) { Meter = meter };
        var entry = BuildEntry(interpreter, caller, facts.At(block, index));
        var attempt = new Attempt
        {
            Terms = terms, Solver = solver, Interpreter = interpreter, Entry = entry, Caller = caller, Block = block, Index = index, Candidate = candidate,
            Anchor = anchor,
        };
        var clock = System.Diagnostics.Stopwatch.StartNew();
        var (discovered, exited, synthesized, validated) = (0L, 0L, 0L, 0L);
        var (syntheses, validations) = (0, 0);
        var notes = new List<string>();
        Outcome Done(Outcome outcome) => outcome with
        {
            Steps = meter.Used,
            Plans = notes.ToImmutableList(),
            Profile = $"发现 {discovered} 出口 {exited - discovered} 合成 {syntheses}/{synthesized} 复核 {validations}/{validated} ms",
        };
        var outcomes = Discover(attempt, out var failure, out var anchored);
        discovered = exited = clock.ElapsedMilliseconds;
        if (outcomes is null) return Done(new(null, failure ?? "比对失败", 0, "") { AnchorFree = !anchored });
        notes.Add($"绑定 {string.Join("，", attempt.Formals.Select((f, i) => $"{(i == 0 ? "this" : (i - 1).ToString())}={solver.Apply(f)}"))}");
        var progress = outcomes.Count == 0 ? 0 : outcomes.Max(o => o.Path.B.Trace.Count);
        var returning = outcomes.Where(o => o.Path.A.Stop?.Kind == StopKind.Return).ToArray();
        if (returning.Length == 0) return Done(new(null, "模板在每条路径上都抛出", progress, "") { AnchorFree = !anchored });
        // 模板返回后调用方抛出的路径不需要出口：替换后它在调用处（求接收者与实参时）或续接里同样抛出，由复核确认。
        // 出口只从继续执行的路径中选，否则这些路径会把区域截在抛出之前。
        if (returning.Where(o => o.Path.B.Stop?.Kind != StopKind.Throw).ToArray() is { Length: > 0 } continuing) returning = continuing;
        var exits = new List<Exit>[returning.Length];
        for (var i = 0; i < returning.Length; i++)
        {
            exits[i] = Exits(attempt, returning[i], out var noExit);
            exited = clock.ElapsedMilliseconds;
            if (InlineTrace.Lines is not null)
                notes.Add($"路径 {i} 轨迹 {string.Join(" ", returning[i].Path.B.Trace.Select(p => $"{p.Block:x}:{p.Statement}{(p.Pending ? "P" : "")}e{p.Events}"))}（模板事件 {returning[i].Path.A.Events}）");
            if (noExit is not null) return Done(new(null, $"没有出口：{noExit}", progress, ""));
        }
        string? last = null;
        foreach (var chosen in Choices(exits))
        {
            notes.Add($"出口 {string.Join(" ", chosen.Select(e => $"{e.Point.Block:x}:{e.Point.Statement}/{e.Covered}"))}");
            foreach (var plan in Plans(attempt, chosen))
            {
                var before = clock.ElapsedMilliseconds;
                syntheses++;
                var replaced = Synthesize(attempt, chosen, plan, out var form, out var why);
                synthesized += clock.ElapsedMilliseconds - before;
                if (replaced is null) { last = why; notes.Add($"{plan.Form}：{why}"); continue; }
                if (useful?.Invoke(replaced) == false) { last = "替换没有覆盖要证的内容"; notes.Add($"{form}：{last}"); continue; }
                before = clock.ElapsedMilliseconds;
                validations++;
                var invalid = Validate(attempt, replaced);
                validated += clock.ElapsedMilliseconds - before;
                if (invalid is not null)
                {
                    last = $"复核不成立：{invalid}";
                    notes.Add($"{form}：{last}");
                    // 诊断：替换后的起点块。
                    if (InlineTrace.Lines is { } print)
                        foreach (var line in print(replaced with { Blocks = replaced.Blocks.Where(b => b.Address == attempt.Block).ToArray(), Regions = [] }))
                            notes.Add($"  替换为 {line}");
                    continue;
                }
                return Done(new(replaced, null, progress, form));
            }
        }
        return Done(new(null, last ?? "没有可合成的替换", progress, ""));
    }

    /// <summary>
    /// 各路径出口的组合。每条路径的出口按覆盖的待证访问从多到少、同样多时从早到晚排列：区域覆盖调用方与模板对应的全部待证访问，
    /// 不多吞调用方自己的代码。先取所有路径共有的出口（续接只有一份），再逐个推后各路径的出口
    /// （例如出口处活跃的局部写不出，推后到它最后一次使用之后）。
    /// </summary>
    private static IEnumerable<Exit[]> Choices(List<Exit>[] found)
    {
        var exits = found.Select(list => list.OrderByDescending(e => e.Covered).ThenBy(e => e.Trace).ToList()).ToArray();
        var seen = new HashSet<string>();
        var common = exits[0].Select(e => (e.Point.Block, e.Point.Statement))
            .Where(p => exits.All(list => list.Any(e => (e.Point.Block, e.Point.Statement) == p))).Take(2);
        foreach (var point in common)
        {
            var chosen = exits.Select(list => list.First(e => (e.Point.Block, e.Point.Statement) == point)).ToArray();
            if (seen.Add(string.Join(",", chosen.Select(e => e.Trace)))) yield return chosen;
        }
        for (var shift = 0; shift < exits.Max(e => e.Count); shift++)
        {
            var chosen = exits.Select(e => e[Math.Min(shift, e.Count - 1)]).ToArray();
            if (seen.Add(string.Join(",", chosen.Select(e => e.Trace)))) yield return chosen;
        }
    }

    /// <summary>
    /// 续接的方案：出口分成组，每组一个目标。只有一组时调用后直接接上目标；两组时调用后按条件分派，条件在每条路径上已定
    /// （真的一组走第一个目标），且能写成调用后的表达式。
    /// </summary>
    private sealed record Plan(IReadOnlyList<(ulong Block, int Index)> Targets, IReadOnlyList<Exit[]> Groups, Func<Exit, Term>? Condition, string Form);

    private const int DispatchLiterals = 4;

    /// <summary>
    /// 方案依次为：所有路径的出口相同（exit）；按返回值分派到两个出口（branch）；按路径条件分派（dispatch：Φ 中把出口分成两组的文字，
    /// 两组可以去同一个目标、带不同的复制，对应调用后调用方自己的分支）；保留其中一个出口的续接（duplicated，复核确认它在各路径上成立）。
    /// </summary>
    private IEnumerable<Plan> Plans(Attempt attempt, Exit[] chosen)
    {
        (ulong, int) PointOf(Exit e) => (e.Point.Block, e.Point.Statement);
        var points = chosen.Select(PointOf).Distinct().ToArray();
        if (points.Length == 1) yield return new Plan(points, [chosen], null, "exit");
        var terms = attempt.Terms;
        var solver = attempt.Solver;
        // 条件把出口分成两组；两个出口时分组须与出口一致。
        Plan? Split(Func<Exit, Term> condition, string form)
        {
            var decided = chosen.Select(e => solver.Decide(e.Path.Path.Phi, condition(e))).ToArray();
            if (decided.Any(d => d is null) || decided.All(d => d == true) || decided.All(d => d == false)) return null;
            var yes = chosen.Where((_, i) => decided[i] == true).ToArray();
            var no = chosen.Where((_, i) => decided[i] == false).ToArray();
            var targets = new[] { yes.Select(PointOf).Distinct().ToArray(), no.Select(PointOf).Distinct().ToArray() };
            if (targets.Any(t => t.Length != 1)) return null;
            if (points.Length == 2 && targets[0][0] == targets[1][0]) return null;
            return new Plan([targets[0][0], targets[1][0]], [yes, no], condition, form);
        }
        if (points.Length == 2 && chosen.All(e => e.Returned is { Width: > 0 }))
        {
            if (Split(e => terms.ToBit(e.Returned!), "branch") is { } truth) yield return truth;
            if (Split(e => terms.Compare(Cond.Eq, e.Returned!, terms.Constant(0, e.Returned!.Width)), "branch") is { } zero) yield return zero;
        }
        if (points.Length <= 2)
        {
            var literals = chosen.SelectMany(e => e.Path.Path.Phi).Select(solver.Apply)
                .Select(l => l.IsOp(OpCode.Not) ? l.Args[0] : l).Where(l => !l.IsConstant && !l.HasFormal)
                .Distinct(ReferenceEqualityComparer.Instance).Cast<Term>();
            var tried = 0;
            foreach (var literal in literals)
            {
                if (Split(_ => literal, "dispatch") is not { } plan) continue;
                yield return plan;
                if (++tried == DispatchLiterals) break;
            }
        }
        if (points.Length == 1) yield break;
        foreach (var point in points.OrderByDescending(p => chosen.Count(e => PointOf(e) == p)))
            yield return new Plan([point], [chosen], null, "duplicated");
    }

    /// <summary>调用前写回实参：形参的绑定写成入口状态下可求值的表达式。</summary>
    private Moment Before(Attempt attempt)
    {
        var locals = new Dictionary<Term, ManagedValue>(ReferenceEqualityComparer.Instance);
        foreach (var (variable, term) in attempt.Entry.Evaluated)
            if (attempt.Caller.LocalOf(variable) is { } local && !attempt.Caller.Cells.Contains(variable)) Hold(attempt, locals, term, local);
        HoldCells(attempt, locals, null);
        return new Moment { Heap = attempt.Entry.Heap, Locals = locals };
    }

    /// <summary>
    /// 结构体局部（存储单元）在入口的各叶子内容也由局部写出：叶子是局部的字段。调用后只在区域内没有改写这个单元时成立（exit 给出时核对）。
    /// </summary>
    private void HoldCells(Attempt attempt, Dictionary<Term, ManagedValue> locals, Exit? exit)
    {
        var interpreter = attempt.Interpreter;
        foreach (var variable in attempt.Caller.Cells)
        {
            if (attempt.Caller.LocalOf(variable) is not { } local || local.Type is not DefinitionRef structure || !interpreter.IsStruct(structure)) continue;
            var leaves = interpreter.Leaves(structure);
            var contents = new Term[leaves.Length];
            var whole = true;
            for (var i = 0; i < leaves.Length; i++)
            {
                var leaf = leaves[i];
                var location = attempt.Terms.CellRoot(0, variable, leaf.Path);
                var content = interpreter.ReadScalar(attempt.Entry.Heap, location, leaf, false);
                if (content is null || exit is not null && !ReferenceEquals(interpreter.ReadScalar(Snapshot(exit.Point), location, leaf, false), content))
                {
                    whole = false;
                    continue;
                }
                contents[i] = content;
                if (!content.IsConstant && leaf.Path.Count > 0 && Chain(local, leaf.Path.Fields) is { } field) locals.TryAdd(content, field);
            }
            // 整个结构体值也是这个局部（全是常量的值照常写成常量）。
            if (whole && leaves.Length > 0 && leaves[0].Path.Count > 0 && contents.Any(c => !c.IsConstant)) locals.TryAdd(attempt.Terms.Tuple(structure, contents), local);
        }
    }

    /// <summary>局部持有的值：标量就是局部；结构体局部的各叶子是局部的字段（不重读局部的来源，重读会带来原代码没有的隐式抛出）。</summary>
    private void Hold(Attempt attempt, Dictionary<Term, ManagedValue> locals, Term term, LocalValue local)
    {
        locals.TryAdd(term, local);
        if (term.Kind != TermKind.Tuple || term.Key is not DefinitionRef structure) return;
        var leaves = attempt.Interpreter.Leaves(structure);
        for (var i = 0; i < leaves.Length && i < term.Args.Length; i++)
            if (!term.Args[i].IsConstant && leaves[i].Path.Count > 0 && Chain(local, leaves[i].Path.Fields) is { } field) locals.TryAdd(term.Args[i], field);
    }

    private ManagedBody? Synthesize(Attempt attempt, Exit[] chosen, Plan plan, out string form, out string? failure)
    {
        form = plan.Form;
        failure = null;
        var caller = attempt.Caller;
        var candidate = attempt.Candidate;
        var method = candidate.Method;
        var definition = method.Method;
        var start = caller.Blocks[attempt.Block];
        var at = start.Statements[attempt.Index].Address;
        var before = Before(attempt) with { Prelude = [], At = at };
        // 实参。
        var arguments = new ManagedValue[definition.Parameters.Count];
        for (var i = 0; i < definition.Parameters.Count; i++)
        {
            var type = method.Concrete(definition.Parameters[i].Type);
            var formal = attempt.Formals[i + 1];
            var bound = attempt.Solver.Apply(formal);
            if (!bound.HasFormal)
            {
                if (Reify(attempt, before, bound, type) is not { } value) { failure = $"实参 {i} 不能写回调用之前（{bound}）"; return null; }
                arguments[i] = value;
            }
            else if (!Mentioned(candidate.Template.Body, i) && type is not ByRefRef)
                arguments[i] = attempt.Interpreter.IsStruct(type) ? new ComposedValue(type, []) : new ConstantValue(0, type, types.ValueWidth(type));
            else { failure = $"实参 {i} 没有确定"; return null; }
        }
        ManagedValue? receiver = null;
        if (!definition.IsStatic && candidate.Kind == ReplacementKind.Call)
        {
            var bound = attempt.Solver.Apply(attempt.Formals[0]);
            if (bound.HasFormal || Reify(attempt, before, bound, null) is not { } self) { failure = "接收者不能写回"; return null; }
            receiver = self;
        }
        if (candidate.Kind == ReplacementKind.BaseConstructor) receiver = new ArgumentValue(-1, caller.Method.DeclaringType, 64);
        // 调用。
        var returnType = method.Concrete(definition.ReturnType);
        LocalValue? result = candidate.Kind == ReplacementKind.Call && !ManagedTypes.IsVoid(returnType) ? newLocal(returnType) : null;
        ManagedStatement call;
        switch (candidate.Kind)
        {
            case ReplacementKind.Construct:
                call = new ManagedAssignment(at, candidate.Constructed!, new NewObjectValue(method, arguments) { Transparent = true });
                break;
            case ReplacementKind.BaseConstructor:
                call = new ManagedCall(at, new ManagedInvocation(method, receiver, arguments, false), null) { Inlined = true };
                break;
            default:
                if (Legality.Dispatched(types, method, receiver) is not { } dispatched) { failure = $"{definition.Name} 可能被重写，调用不一定到这个方法体"; return null; }
                call = new ManagedCall(at, new ManagedInvocation(method, receiver, arguments, dispatched), result) { Inlined = true };
                break;
        }
        // 续接：每个目标的调用后赋值（活跃局部）、多出的写入与出口语句的改写。
        // 调用方多出的写入在每条路径上都发生在第一个事件之前、且能在入口写出时，放到调用之前：之后的事件可能读到它。
        var moved = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var early = new List<ManagedStatement>();
        // 与续接相同，覆盖结构体字段全部叶子的写入按整体写出（叶子可能不可访问）；整体写入的每个叶子都要在第一个事件之前。
        foreach (var (location, value) in Whole(attempt, OwnWrites(attempt, chosen[0]).ToList()))
        {
            var parts = Parts(attempt, location, value);
            if (!chosen.All(e => parts.All(p => Early(e, p.Location, p.Value))) || Location(attempt, before, location, Use.Write) is not { } place
                || Reify(attempt, before, value, place.Type) is not { } written) continue;
            moved.Add(location);
            foreach (var part in parts) moved.Add(part.Location);
            early.Add(new ManagedStore(at, place, written));
        }
        if (early.Count > 0) form += "+early";
        // 异常边赋值（5.6）：处理块入口活跃的局部在区域内第一个事件（可能抛出）处已与入口不同时，在调用之前赋好。
        if (caller.HandlerOf(attempt.Block) is { } region)
        {
            var guarded = new List<ManagedCopy>();
            foreach (var variable in caller.LiveBefore(region.HandlerEntry, 0).OrderBy(v => v.ToString(), StringComparer.Ordinal))
            {
                if (caller.LocalOf(variable) is not { } local || caller.Cells.Contains(variable)) continue;
                // 没有事件的路径上调用不会因区域内的事件抛出，不约束这个值。
                var values = chosen.Select(e => AtFirstEvent(e.Path.Path.B.Trace, variable)).OfType<Term>().Distinct(ReferenceEqualityComparer.Instance).ToArray();
                if (values is not [Term value]) continue;
                if (chosen[0].Path.Path.B.Trace[0].Env.TryGetValue(variable, out var entry) && ReferenceEquals(entry, value)) continue;
                if (Reify(attempt, before, value, local.Type) is { } written) guarded.Add(new ManagedCopy(local, written));
            }
            if (guarded.Count > 0)
            {
                early.AddRange(Sequential(guarded, at));
                form += "+handler";
            }
        }
        var statements = new List<ManagedStatement>();
        var edges = new List<ManagedEdge>();
        IReadOnlyList<ManagedStatement>? tail = null;
        List<ManagedCopy>? prior = null;
        for (var t = 0; t < plan.Targets.Count; t++)
        {
            var target = plan.Targets[t];
            var group = plan.Groups[t];
            if (target.Block == attempt.Block && target.Index < attempt.Index) { failure = "出口回到起点之前"; return null; }
            if (Continuation(attempt, group, target, result, moved, out var priors, out var copies, out var stores, out var rewritten, out var why) is false)
            {
                failure = why;
                return null;
            }
            // 调用前的赋值只有一份：各目标须相同。
            if (prior is null) prior = priors;
            else if (prior.Count != priors.Count || prior.Zip(priors).Any(p => !p.First.Target.Variable.Equals(p.Second.Target.Variable) || !Cpp2CS.Managed.ManagedStructure.Value(p.First.Value, p.Second.Value)))
            { failure = "调用前的赋值在各目标上不同"; return null; }
            if (copies.Count > 0) form += "+copies";
            if (stores.Count > 0) form += "+writes";
            // 出口与起点在同一块时接上块里余下的语句：跳到这个块会回到起点，重复执行区域。
            var needsTail = target.Index > 0 || target.Block == attempt.Block || rewritten is not null || stores.Count > 0;
            if (needsTail)
            {
                if (plan.Targets.Count > 1) { failure = "分派的出口在块中间"; return null; }
                // 出口块余下的语句并入起点块，须在同一个异常处理上下文中：不把语句搬进或搬出 try。
                if (caller.HandlerOf(target.Block)?.HandlerEntry != caller.HandlerOf(attempt.Block)?.HandlerEntry)
                { failure = "出口块与起点块的异常处理上下文不同，余下的语句不能并入起点块"; return null; }
                // 出口在块中间（或在起点块、出口语句要改写）：调用后依次赋值，接上出口块余下的语句。
                var sequential = Sequential(copies, at);
                statements.AddRange(sequential);
                statements.AddRange(stores);
                var rest = caller.Blocks[target.Block].Statements.Skip(target.Index).ToList();
                if (rewritten is not null) rest[0] = rewritten;
                tail = rest;
                edges.Add(null!);
            }
            else edges.Add(new ManagedEdge(target.Block, copies));
        }
        // 值的写法需要的语句（对象初始化器）按入口值写，放在提前的写入之前。
        if (before.Prelude!.Count > 0)
        {
            early.InsertRange(0, before.Prelude);
            form += "+initializer";
        }
        // 调用前赋值的局部（5.4 的调用前写法）不能是实参、提前的写入里按入口值用到的局部：赋值放在它们之前。
        if (prior is { Count: > 0 })
        {
            var uses = early.Append(call).SelectMany(Program.Uses).ToHashSet();
            if (prior.FirstOrDefault(c => uses.Contains(c.Target.Variable)) is { } clash)
            { failure = $"调用前赋值的 {clash.Target.Variable} 在调用或提前的写入中按入口值用到"; return null; }
            early.InsertRange(0, Sequential(prior, at));
            form += "+prior";
        }
        statements.InsertRange(0, start.Statements.Take(attempt.Index).Concat(early).Append(call));
        if (tail is not null) statements.AddRange(tail);
        else if (plan.Condition is { } condition)
        {
            // 条件在各路径上写成同一个调用后的表达式（在条件取常量的路径上它就是那个常量，不写）。分派在出口边的复制之前，
            // 此时局部仍是区域入口的值（调用前赋过的除外）。
            var assigned = early.SelectMany(Program.Definitions).ToHashSet();
            var held = new Dictionary<Term, ManagedValue>(ReferenceEqualityComparer.Instance);
            foreach (var (variable, term) in attempt.Entry.Evaluated)
                if (caller.LocalOf(variable) is { } local && !caller.Cells.Contains(variable) && !assigned.Contains(variable)) Hold(attempt, held, term, local);
            HoldCells(attempt, held, null);
            ManagedValue? written = null;
            foreach (var exit in chosen)
            {
                var term = attempt.Solver.Apply(condition(exit));
                if (term.IsConstant) continue;
                if (Reify(attempt, After(attempt, exit, result) with { Locals = held }, term, types.Boolean) is not { } value) { failure = $"分派条件不能写成调用后的值（{term}）"; return null; }
                if (written is null) written = value;
                else if (!Cpp2CS.Managed.ManagedStructure.Value(written, value)) { failure = "分派条件在各路径上的写法不同"; return null; }
            }
            if (written is null) { failure = "分派条件在各路径上都是常量"; return null; }
            statements.Add(new ManagedBranch(at, written, edges[0], edges[1]));
        }
        else statements.Add(new ManagedJump(at, edges[0]));
        var blocks = caller.Body.Blocks.Select(b => b.Address == attempt.Block ? new ManagedBlock(b.Address, statements) : b).ToList();
        return Prune(caller.Body with { Blocks = blocks });
    }

    /// <summary>轨迹中第一个事件语句处局部的值；没有事件时为 null。</summary>
    private static Term? AtFirstEvent(IReadOnlyList<TracePoint> trace, Variable variable)
    {
        for (var i = 0; i + 1 < trace.Count; i++)
            if (trace[i + 1].Events > trace[i].Events) return trace[i].Env.GetValueOrDefault(variable);
        return null;
    }

    private static bool Mentioned(ManagedBody body, int index) => body.Blocks.SelectMany(b => b.Statements)
        .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
        .Any(v => v is ArgumentValue argument && argument.Index == index);

    /// <summary>调用后的时刻：模板在这条路径上的最终堆、返回值与未在区域内改写的局部。</summary>
    private Moment After(Attempt attempt, Exit exit, LocalValue? result)
    {
        var locals = new Dictionary<Term, ManagedValue>(ReferenceEqualityComparer.Instance);
        foreach (var (variable, term) in attempt.Entry.Evaluated)
            if (attempt.Caller.LocalOf(variable) is { } local && !attempt.Caller.Cells.Contains(variable)
                && (!exit.Point.Env.TryGetValue(variable, out var now) || ReferenceEquals(now, term)))
                Hold(attempt, locals, term, local);
        HoldCells(attempt, locals, exit);
        if (attempt.Candidate is { Kind: ReplacementKind.Construct, Constructed: { } constructed } && exit.Point.Env.TryGetValue(constructed.Variable, out var created))
            locals[created] = constructed;
        return new Moment { Heap = Applied(attempt.Solver, exit.Path.Path.A), Result = exit.Returned is { } r ? attempt.Solver.Apply(r) : null, ResultLocal = result, Locals = locals };
    }

    /// <summary>代入绑定后的模板状态：写入表中的形参换成调用方的值。</summary>
    private static SideState Applied(Solver solver, SideState side) => new()
    {
        Frames = [], Version = side.Version, Exposed = side.Exposed, Fresh = side.Fresh,
        Writes = ImmutableList.CreateRange(side.Writes.Select(w => (solver.Apply(w.Location), solver.Apply(w.Value)))),
    };

    /// <summary>
    /// 一个出口的续接：出口处活跃、在区域内被改写的局部写成调用后的表达式（各路径必须一致）；调用方在区域内多出的写入移到调用之后；
    /// 出口语句含待证访问时以调用后的值改写。
    /// </summary>
    private bool Continuation(Attempt attempt, Exit[] group, (ulong Block, int Index) target, LocalValue? result, IReadOnlySet<Term> moved,
        out List<ManagedCopy> priors, out List<ManagedCopy> copies, out List<ManagedStatement> stores, out ManagedStatement? rewritten, out string? failure)
    {
        priors = [];
        copies = [];
        stores = [];
        rewritten = null;
        failure = null;
        var caller = attempt.Caller;
        var interpreter = attempt.Interpreter;
        var statement = caller.Blocks[target.Block].Statements[target.Index];
        var at = statement.Address;
        // 续接由停在目标处的出口写出；保留一个出口的续接（duplicated）时，其他路径在复核中确认。
        var present = group.Where(e => (e.Point.Block, e.Point.Statement) == target).ToArray();
        if (present.Length == 0) { failure = "没有路径停在续接的目标处"; return false; }
        // 每个出口处活跃的局部在调用后的写法；写不出的（区域内算出、调用后取不到的值）先记下。
        var expressions = new Dictionary<Variable, ManagedValue?>();
        var prior = new Dictionary<Variable, ManagedValue>();
        var blocked = new Dictionary<Variable, string>();
        foreach (var variable in caller.LiveBefore(target.Block, target.Index).OrderBy(v => v.ToString(), StringComparer.Ordinal))
        {
            if (caller.LocalOf(variable) is not { } local) continue;
            if (Expression(attempt, present, local, result, out var reason) is var (changed, value, early) && reason is null)
            {
                if (early) prior[variable] = value!;
                else expressions[variable] = changed ? value : null;
            }
            else blocked[variable] = reason!;
        }
        // 出口语句里用到写不出的局部或待证访问：这些子值换成调用后的表达式（如返回值），局部就不再需要。
        if (blocked.Count > 0 || HasPending(statement))
        {
            ManagedStatement? first = null;
            foreach (var exit in present)
            {
                if (RewriteExit(attempt, exit, statement, blocked.Keys.ToHashSet(), result, out var why) is not { } mapped) { failure = why; return false; }
                if (first is null) first = mapped;
                else if (!Cpp2CS.Managed.ManagedStructure.Same(first, mapped)) { failure = "出口语句在各路径上的改写不同"; return false; }
            }
            rewritten = first;
            var live = caller.LiveThrough(target.Block, target.Index);
            foreach (var defined in Program.Definitions(statement)) live.Remove(defined);
            live.UnionWith(Program.Uses(rewritten!));
            if (blocked.FirstOrDefault(b => live.Contains(b.Key)) is { Value: { } reason }) { failure = reason; return false; }
            foreach (var variable in expressions.Keys.Where(v => !live.Contains(v)).ToArray()) expressions.Remove(variable);
            foreach (var variable in prior.Keys.Where(v => !live.Contains(v)).ToArray()) prior.Remove(variable);
            if (ReferenceEquals(rewritten, statement) || Cpp2CS.Managed.ManagedStructure.Same(rewritten!, statement)) rewritten = null;
        }
        foreach (var (variable, expression) in expressions)
            if (expression is not null && !(expression is LocalValue same && same.Variable.Equals(variable)))
                copies.Add(new ManagedCopy(caller.LocalOf(variable)!, expression));
        foreach (var (variable, expression) in prior)
            if (!(expression is LocalValue same && same.Variable.Equals(variable)))
                priors.Add(new ManagedCopy(caller.LocalOf(variable)!, expression));
        // 调用方多出的公共写入（已放到调用之前的除外）移到调用之后：取停在目标处的出口的区域。出口更远的路径在区域里多做的写入
        // 由续接再做一次，不在调用后重复写出。
        foreach (var exit in present)
        {
            var moment = After(attempt, exit, result);
            foreach (var (location, value) in Whole(attempt, OwnWrites(attempt, exit).ToList()))
            {
                if (moved.Contains(location)) continue;
                if (Location(attempt, moment, location, Use.Write) is not { } place)
                { failure = $"调用方在区域内对 {location} 的写入不能移到调用之后（位置写不出）"; return false; }
                if (Reify(attempt, moment, value, place.Type) is not { } written)
                { failure = $"调用方在区域内对 {location} 的写入不能移到调用之后（值 {value} 写不出）"; return false; }
                var store = new ManagedStore(at, place, written);
                if (exit != present[0] && !stores.Any(s => Cpp2CS.Managed.ManagedStructure.Same(s, store))) { failure = "调用方多出的写入在各路径上不同"; return false; }
                if (exit == present[0]) stores.Add(store);
            }
        }
        return true;
    }

    /// <summary>
    /// 局部在各出口处的值写成调用后的表达式；在区域内没有改变时 Changed 为假。各路径须是同一个写法；
    /// 写法不同时取唯一依赖返回值的那个（返回常量的路径上它就等于那个常量，例如 res != 0 在返回 1 的路径上为真），由复核确认。
    /// </summary>
    private (bool Changed, ManagedValue? Value, bool Prior) Expression(Attempt attempt, Exit[] group, LocalValue local, LocalValue? result, out string? failure)
    {
        failure = null;
        var caller = attempt.Caller;
        var variable = local.Variable;
        var entryValue = attempt.Entry.Value(local);
        var written = new List<ManagedValue>();
        var changed = false;
        foreach (var exit in group)
        {
            Term now;
            if (caller.Cells.Contains(variable))
            {
                if (attempt.Interpreter.ReadValue(Snapshot(exit.Point), attempt.Terms.CellRoot(0, variable, FieldPath.Empty), local.Type, false) is not { } content)
                { failure = $"局部 {variable} 的内容不可判定"; return default; }
                now = content;
            }
            else now = exit.Point.Env.TryGetValue(variable, out var assigned) ? assigned : entryValue;
            if (ReferenceEquals(now, entryValue) && !changed) continue;
            changed = true;
            if (Reify(attempt, After(attempt, exit, result), now, local.Type) is not { } value)
            {
                // 调用后写不出（例如读取的位置之后经过屏障）时取调用前的写法：各路径上是同一个入口可求值的项，在调用之前赋值。
                if (Prior(attempt, group, local) is { } prior) return (true, prior, true);
                failure = $"出口处活跃的 {variable} 不能写成调用后的值（{now}）";
                return default;
            }
            if (!written.Any(w => Cpp2CS.Managed.ManagedStructure.Value(w, value))) written.Add(value);
        }
        if (written.Count <= 1) return (changed, written.FirstOrDefault(), false);
        var general = written.Where(w => result is not null && ManagedValues.Walk(w).OfType<LocalValue>().Any(l => l.Variable.Equals(result.Variable))).ToArray();
        if (general.Length != 1) { failure = $"出口处活跃的 {variable} 在各路径上不同"; return default; }
        return (changed, general[0], false);
    }

    /// <summary>局部在各出口处是同一个项、且能在入口写出时，它在调用前的写法（5.4）。取址的局部不提前：模板可能经地址观察它。</summary>
    private ManagedValue? Prior(Attempt attempt, Exit[] group, LocalValue local)
    {
        if (attempt.Caller.Cells.Contains(local.Variable)) return null;
        var entryValue = attempt.Entry.Value(local);
        var values = group.Select(e => e.Point.Env.TryGetValue(local.Variable, out var now) ? now : entryValue).Distinct(ReferenceEqualityComparer.Instance).ToArray();
        return values is [Term only] ? Reify(attempt, Before(attempt), only, local.Type) : null;
    }

    /// <summary>
    /// 出口语句的改写：读到写不出的局部或待证访问的子值，按这条路径上求得的项写成调用后的表达式（取最大的子值）。
    /// 改写后仍读到它们时失败。
    /// </summary>
    private ManagedStatement? RewriteExit(Attempt attempt, Exit exit, ManagedStatement statement, IReadOnlySet<Variable> blocked, LocalValue? result, out string? failure)
    {
        var moment = After(attempt, exit, result);
        string? why = null;
        bool Blocked(ManagedValue value) => ManagedValues.Walk(value).Any(v => v is LocalValue local && blocked.Contains(local.Variable));
        bool Needs(ManagedValue value) => Blocked(value) || ManagedValues.Walk(value).Any(v => v is FieldValue { Pending: not null } or StaticFieldValue { Pending: not null });
        // 写不出的局部必须消去；待证访问能写成调用后的值就写（用处替换），写不出时原样留给之后的证明。
        ManagedValue Rewrite(ManagedValue value)
        {
            if (why is not null || !Needs(value)) return value;
            if (exit.Point.Nodes.TryGetValue(value, out var term) && Reify(attempt, moment, attempt.Solver.Apply(term), value.Type) is { } replaced && !Blocked(replaced))
                return replaced;
            if (value is LocalValue) { why = $"出口语句中的 {value} 不能写成调用后的值"; return value; }
            return ManagedValues.Map(value, Rewrite);
        }
        ManagedValue Target(ManagedValue target) => !Blocked(target) || target is LocalValue ? target : ManagedValues.Map(target, Rewrite);
        var mapped = ManagedValues.Map(statement, Rewrite, Target);
        failure = why;
        return why is null ? mapped : null;
    }

    /// <summary>调用方在区域内多出的公共写入：出口处调用方写过、而模板（代入绑定后）在这条路径上没有同样写入（Φ 下相同）的位置。</summary>
    private IEnumerable<(Term Location, Term Value)> OwnWrites(Attempt attempt, Exit exit)
    {
        var interpreter = attempt.Interpreter;
        var template = Applied(attempt.Solver, exit.Path.Path.A);
        var snapshot = Snapshot(exit.Point);
        var phi = exit.Path.Path.Phi;
        foreach (var (location, value) in exit.Point.Writes)
        {
            if (TermTable.Immutable(location) || interpreter.Private(snapshot, location)) continue;
            var leaf = new Leaf(FieldPath.Empty, value.Hint ?? types.Int32, value.Width, value.Bit);
            if (interpreter.ReadScalar(template, attempt.Solver.Fold(phi, location), leaf, false) is { } written
                && ReferenceEquals(attempt.Solver.Fold(phi, written), attempt.Solver.Fold(phi, value))) continue;
            yield return (location, value);
        }
    }

    /// <summary>
    /// 结构体的整体写入在执行中拆成各叶子的写入；写回时，覆盖某个结构体字段全部叶子的写入合成对这个字段的一次整体写入（取最外层的结构体字段），
    /// 写在其中第一个叶子的位置。
    /// </summary>
    private List<(Term Location, Term Value)> Whole(Attempt attempt, List<(Term Location, Term Value)> writes)
    {
        var terms = attempt.Terms;
        var interpreter = attempt.Interpreter;
        var values = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        foreach (var (location, value) in writes) values.TryAdd(location, value);
        var consumed = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var result = new List<(Term, Term)>();
        foreach (var (location, value) in writes)
        {
            if (consumed.Contains(location)) continue;
            var path = TermTable.PathOf(location);
            (Term, Term)? grouped = null;
            for (var keep = 1; keep < path.Count && grouped is null; keep++)
            {
                if (FieldType(path.Fields[keep - 1]) is not DefinitionRef structure || !interpreter.IsStruct(structure)) continue;
                if (terms.Truncate(location, keep) is not { } root) continue;
                var leaves = interpreter.Leaves(structure);
                var parts = new Term[leaves.Length];
                var all = true;
                for (var i = 0; i < leaves.Length && all; i++)
                    all = leaves[i].Path.Count > 0 && values.TryGetValue(terms.Append(root, leaves[i].Path), out parts[i]!);
                if (!all) continue;
                foreach (var leaf in leaves) consumed.Add(terms.Append(root, leaf.Path));
                grouped = (root, terms.Tuple(structure, parts));
            }
            if (grouped is { } whole) result.Add(whole);
            else
            {
                consumed.Add(location);
                result.Add((location, value));
            }
        }
        return result;
    }

    /// <summary>整体写入（Whole 合成的结构体值）拆回各叶子的写入；其他写入就是它本身。</summary>
    private static List<(Term Location, Term Value)> Parts(Attempt attempt, Term location, Term value) =>
        value.Kind == TermKind.Tuple && value.Key is DefinitionRef structure
            ? attempt.Interpreter.Leaves(structure).Select((leaf, i) => (attempt.Terms.Append(location, leaf.Path), value.Args[i])).ToList()
            : [(location, value)];

    /// <summary>这条路径上调用方的这次写入发生在第一个事件之前。</summary>
    private static bool Early(Exit exit, Term location, Term value)
    {
        var trace = exit.Path.Path.B.Trace;
        for (var j = 0; j <= exit.Trace && j < trace.Count; j++)
            if (trace[j].Writes.Contains((location, value))) return trace[j].Events == 0;
        return false;
    }

    /// <summary>并行赋值写成依次赋值：目标在其他值中被读到时先存入临时局部。</summary>
    private List<ManagedStatement> Sequential(List<ManagedCopy> copies, ulong at)
    {
        var result = new List<ManagedStatement>();
        var targets = copies.Select(c => c.Target.Variable).ToHashSet();
        var direct = new List<ManagedCopy>();
        foreach (var copy in copies)
        {
            var interferes = copies.Any(other => other != copy && ManagedValues.Walk(other.Value).OfType<LocalValue>().Any(l => l.Variable.Equals(copy.Target.Variable)));
            if (!interferes) { direct.Add(copy); continue; }
            var temp = newLocal(copy.Target.Type);
            result.Add(new ManagedAssignment(at, temp, copy.Value));
            direct.Add(copy with { Value = temp });
        }
        result.AddRange(direct.Select(c => new ManagedAssignment(at, c.Target, c.Value)));
        return result;
    }

    /// <summary>删去不可达的块（从入口与仍有 try 块的处理块出发），清理区域列表。</summary>
    private static ManagedBody Prune(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var reachable = new HashSet<ulong>();
        var pending = new Stack<ulong>();
        void Reach(ulong address) { if (blocks.ContainsKey(address) && reachable.Add(address)) pending.Push(address); }
        Reach(body.Blocks[0].Address);
        for (var changed = true; changed;)
        {
            changed = false;
            while (pending.TryPop(out var address))
                foreach (var edge in blocks[address].Statements.SelectMany(ManagedValues.Edges)) Reach(edge.Target);
            foreach (var region in body.Regions)
                if (region.Try.Any(reachable.Contains) && !reachable.Contains(region.HandlerEntry) && blocks.ContainsKey(region.HandlerEntry))
                {
                    Reach(region.HandlerEntry);
                    changed = true;
                }
        }
        return body with
        {
            Blocks = body.Blocks.Where(b => reachable.Contains(b.Address)).ToArray(),
            Regions = body.Regions.Where(r => r.Try.Any(reachable.Contains)).Select(r => r with
            {
                Try = r.Try.Where(reachable.Contains).ToArray(),
                Handler = r.Handler.Where(reachable.Contains).ToArray(),
            }).ToArray(),
        };
    }

    /// <summary>复核：原方法体与新方法体从起点共同执行（新调用展开为模板），每条路径都要在同一未改动的块入口状态相等，或同样返回、同样抛出。</summary>
    private string? Validate(Attempt attempt, ManagedBody replaced)
    {
        var oldProgram = attempt.Caller;
        var newProgram = Program.Compile(replaced, types);
        var unchanged = new HashSet<ulong>(replaced.Blocks.Where(b => b.Address != attempt.Block && oldProgram.Blocks.TryGetValue(b.Address, out var old) && ReferenceEquals(old, b))
            .Select(b => b.Address));
        var solver = new Solver(attempt.Terms, types);
        var interpreter = new Interpreter(types, solver, evidence) { Meter = attempt.Interpreter.Meter };
        var validation = new Attempt
        {
            Terms = attempt.Terms, Solver = solver, Interpreter = interpreter, Entry = attempt.Entry, Caller = oldProgram, Block = attempt.Block,
            Index = attempt.Index, Candidate = attempt.Candidate, Anchor = attempt.Anchor,
        };
        var oldSide = CallerSide(validation, oldProgram, false);
        var newSide = CallerSide(validation, newProgram, false);
        // 新方法体中构造由 newobj 完成，不需要合成的分配。
        newSide.AllocationTarget = null;
        newSide.Stop = null;
        var path = new JointPath
        {
            A = WithUnchanged(oldSide, unchanged), B = WithUnchanged(newSide, unchanged), Phi = attempt.Entry.Phi,
        };
        var joint = new Joint(interpreter, templates, JointMode.Validation) { PathBudget = 512 };
        var outcomes = joint.Run(path, true);
        return outcomes.FirstOrDefault(o => !o.Success)?.Failure;
    }

    private static SideState WithUnchanged(SideState side, IReadOnlySet<ulong> unchanged) => new()
    {
        Frames = side.Frames, Writes = side.Writes, Initialized = side.Initialized, Entry = side.Entry, Unchanged = unchanged,
        AllocationTarget = side.AllocationTarget, Stop = side.Stop,
    };
}

/// <summary>写出的调用的合法性：分派、访问权限。</summary>
internal static class Legality
{
    /// <summary>
    /// 还原的调用是否写成 callvirt；不能写成调用时为 null。证明说的是这个方法体本身，调用不能分派到别的方法体：
    /// 非虚方法的 callvirt 只多一次判空；接收者是调用方的 this 时写成非虚调用；其他接收者须没有可能的重写。
    /// </summary>
    public static bool? Dispatched(ManagedTypes types, MethodRef method, ManagedValue? receiver)
    {
        var definition = method.Method;
        if (definition.IsStatic || definition.Name == ".ctor") return false;
        if (!definition.IsVirtual || (definition.Attributes & MethodAttributes.Final) != 0 || definition.Owner.IsValueType) return true;
        if (receiver is ArgumentValue { Index: -1 }) return false;
        return receiver?.Type is DefinitionRef type && !Overridden(types, definition, type.Definition) ? true : null;
    }

    private static bool Overridden(ManagedTypes types, MethodDef method, TypeDef receiver)
    {
        static bool Reaches(TypeDef type, TypeDef ancestor)
        {
            for (TypeRef? at = type.BaseType; at is DefinitionRef definition; at = definition.Definition.BaseType)
                if (ReferenceEquals(definition.Definition, ancestor)) return true;
            return false;
        }
        bool Redefines(TypeDef type) => type.Methods.Any(m => m.IsVirtual && m.Slot == method.Slot);
        for (var at = receiver; !ReferenceEquals(at, method.Owner); at = at.BaseType is DefinitionRef parent ? parent.Definition : method.Owner)
            if (Redefines(at)) return true;
        return types.Model.Types.Any(t => Reaches(t, receiver) && Redefines(t));
    }
}
