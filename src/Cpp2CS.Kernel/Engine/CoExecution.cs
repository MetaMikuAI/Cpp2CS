using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Kernel.Engine;

/// <summary>共同执行的结论。Proved 之外的各项是反驳的类别（设计 15：正向核对把“理论不够”与缺数据分开）。</summary>
public enum Verdict : byte
{
    Proved,
    /// <summary>缺事实：现场有未命名、未定位的效果，或事实层不能回答。</summary>
    MissingFact,
    /// <summary>缺独立关系的行：两个位置不能证明不重叠，或一次越过没有依据。</summary>
    MissingIndependence,
    /// <summary>对应不成立，或用到了尚未实现的理论（环上的切点配对、展开路径、运行时内联体）。</summary>
    Insufficient,
    /// <summary>步数预算耗尽。</summary>
    Budget,
}

/// <summary>共同执行的结果。Assumptions 是用到的有定义条件（设计 9.1）。</summary>
public sealed record ProofResult(Verdict Verdict, string Detail, int Paths, int Steps, ImmutableArray<string> Assumptions);

/// <summary>
/// 共同执行（设计 9.3）：现场（原生快照）与模板（按目录展开的效果图）从入口出发，在共享的路径条件下同步推进。
/// 两侧的值都写成现场一侧的项：模板的形参按调用约定绑定到入口槽位，事件的结果在事件对上之后绑定。
/// 任何一侧的分支在路径条件下可判定时走确定的一侧，否则分叉；事件逐个同种、同操作数，
/// 事件与结局处双方写过的位置内容相同。引擎不按托管操作的种类分支：它只认效果的种类。
///
/// 内存按设计 7.4 分类：相对入口栈指针常量偏移的是帧对象，地址没有逃逸时不可观察；映像数据区里的是运行时私有状态与元数据槽；
/// 其余是托管堆与运行时结构，读取的身份是（地址，沿本侧的写入往回最近的可能改写它的定义）。
/// </summary>
public sealed partial class CoExecution
{
    private sealed class Refuted(Verdict verdict, string detail) : Exception(detail)
    {
        public Verdict Verdict => verdict;
        /// <summary>原因是引擎还没有实现设计里的某一部分（环上的切点配对、展开出口、由跳转完成的调用）。</summary>
        public bool Unsupported { get; init; }
    }

    /// <summary>一侧的位置与环境。Visits 是这条路径上各块已进入的次数。</summary>
    private sealed record Side(BlockId Block, int Index, ImmutableDictionary<Term, Term> Env, ImmutableDictionary<int, int> Visits,
        ExceptionKind Thrown = ExceptionKind.None);

    /// <summary>一次堆上的写入，以及写入之后本侧的内存版本。</summary>
    private readonly record struct Store(Term Address, Term Value, Term Version);

    /// <summary>
    /// 模板一侧正在展开的一次调用（设计 9.2：调用的含义来自被调方法的效果图）：被调方法自己的原生快照。
    /// 入口槽位按调用约定绑定到实参，其余槽位是这次展开独有的符号；它的帧是另一个帧，它在堆上的读写记在模板一侧。
    /// Continue 是模板在这次调用之后的位置，Result 是模板里代表调用结果的项。
    /// </summary>
    private sealed record Inner(MethodSnapshot Snapshot, Side Side, Term StackPointer, int Instance,
        ImmutableDictionary<long, Term> Frame, int FrameGeneration, Side Continue, Term? Result, ImmutableArray<(Slot Slot, int Bits)>? Returned);

    private sealed record State(Side Native, Side Template, PathConditions Conditions, int Epoch, int Serial, int FrameGeneration,
        ImmutableList<Store> NativeWrites, ImmutableList<Store> TemplateWrites, ImmutableDictionary<long, Term> Frame)
    {
        public Inner? Inner { get; init; }
        /// <summary>这条路径上已经展开的调用数，以及已经引入的任意值的个数。</summary>
        public int Inlines { get; init; }
        public int Fresh { get; init; }
        /// <summary>证明一条声明时，这条路径上与声明有关的记录（见 CoExecution.Claims.cs）。</summary>
        public Trail? Trail { get; init; }
    }

    private enum Role : byte { Native, Template, Inner }

    private enum EventKind : byte { Fork, Call, Throw, Return, Initialize, Trap, Vacuous, Allocate, Landing, Departed }

    private sealed record Event(EventKind Kind)
    {
        public ImmutableArray<(ImmutableArray<(Term Condition, bool Value)> Literals, Side Next)> Arms { get; init; } = [];
        public Side? After { get; init; }
        public ExceptionKind Exception { get; init; }
        public ImmutableArray<Term> Values { get; init; } = [];
        public ulong Address { get; init; }
        public OccurrenceId Occurrence { get; init; }
        public TemplateEffect? Effect { get; init; }
        public Term? Class { get; init; }
    }

    private const int MemoryVersion = 1005;

    private readonly MethodSnapshot native;
    private FlowGraph<TemplateEffect> template;
    private readonly PlacedGraph nativeGraph;
    private PlacedGraph templateGraph;
    private readonly MethodBody body;
    private readonly INativeFacts facts;
    private readonly Func<ulong, MethodSnapshot?>? snapshots;
    private readonly TermPool terms;
    private readonly int budget;
    private readonly SortedSet<string> assumptions = new(StringComparer.Ordinal);
    private readonly Term stackPointer;
    private int steps, paths;
    /// <summary>最近一次原生读写落在托管堆上（不是帧对象，也不是映像数据区）。</summary>
    private bool heapAccess;

    private CoExecution(MethodSnapshot native, FlowGraph<TemplateEffect> template, MethodBody body, INativeFacts facts,
        Func<ulong, MethodSnapshot?>? snapshots, int budget)
    {
        this.snapshots = snapshots;
        if (!ReferenceEquals(native.Terms, template.Terms)) throw new ArgumentException("两侧须共用一个项池");
        this.native = native;
        this.template = template;
        this.body = body;
        this.facts = facts;
        this.budget = budget;
        terms = native.Terms;
        nativeGraph = new PlacedGraph(native);
        templateGraph = new PlacedGraph(template);
        stackPointer = Entry(new Slot(SlotKind.StackPointer, 0));
    }

    /// <summary>
    /// 核对一个方法：原生快照与它的真实 IL 按目录展开的效果图是否等价。两张图须建在同一个项池里，模板的图号大于 0。
    /// snapshots 按入口地址给出别的方法的快照（可以属于别的项池），展开调用时使用；没有时为空。
    /// </summary>
    public static ProofResult Check(MethodSnapshot native, FlowGraph<TemplateEffect> template, MethodBody body, INativeFacts facts,
        Func<ulong, MethodSnapshot?>? snapshots = null, int budget = 200_000)
    {
        CoExecution? engine = null;
        try
        {
            engine = new CoExecution(native, template, body, facts, snapshots, budget);
            engine.Run();
            return new(Verdict.Proved, "", engine.paths, engine.steps, [.. engine.assumptions]);
        }
        catch (Refuted refuted)
        {
            return new(refuted.Verdict, refuted.Message, engine?.paths ?? 0, engine?.steps ?? 0, [.. engine?.assumptions ?? []]);
        }
    }

    // ---- 入口与调用约定 ----

    private Term Entry(Slot slot)
    {
        foreach (var parameter in native.EntryParameters)
            if (parameter.Slot == slot) return parameter;
        throw new Refuted(Verdict.MissingFact, $"快照的入口没有声明槽位 {slot}");
    }

    /// <summary>
    /// 托管签名的各形参与返回值落在哪些槽位：每个值是一串（槽位，位宽），依次是值的低位到高位，各取所在槽位的低位。
    /// 整数、引用、地址依次占整数槽，浮点依次占向量槽；值类型按规格登记的传递方式（AggregateConvention）。
    /// 生成代码在末尾另有一个隐含的方法指针实参，不属于托管签名。经栈传递的实参尚未登记。
    /// </summary>
    private static ImmutableArray<ImmutableArray<(Slot Slot, int Bits)>> Convention(MethodShape method, out ImmutableArray<(Slot Slot, int Bits)>? result)
    {
        var slots = ImmutableArray.CreateBuilder<ImmutableArray<(Slot, int)>>(method.Parameters.Length);
        int integers = 0, vectors = 0;
        foreach (var parameter in method.Parameters) slots.Add(Place(parameter, ref integers, ref vectors, "实参"));
        if (integers > 7 || vectors > 8) throw new Refuted(Verdict.MissingFact, "经栈传递的实参没有登记");
        result = null;
        if (method.Return is { } returned)
        {
            // 返回值放在它作为第一个实参时所用的寄存器里（AAPCS64 §6.9）。
            int first = 0, firstVector = 0;
            result = Place(returned, ref first, ref firstVector, "返回值");
        }
        return slots.MoveToImmutable();
    }

    /// <summary>一个值从第 integers 个整数槽、第 vectors 个向量槽起放在哪里。</summary>
    private static ImmutableArray<(Slot Slot, int Bits)> Place(TypeShape type, ref int integers, ref int vectors, string what)
    {
        if (type.Kind != StackKind.Value)
            return type.Kind is StackKind.Float32 or StackKind.Float64 ? [(new Slot(SlotKind.Vector, vectors++), type.StorageBits)]
                : [(new Slot(SlotKind.Integer, integers++), type.StorageBits)];
        var rules = AggregateConvention.Aapcs64;
        switch (rules.Classify(type.StorageBits, type.Members))
        {
            case AggregatePlacement.IntegerSlots:
            {
                int count = rules.SlotsFor(type.StorageBits), slotBits = rules.SlotBytes * 8;
                var pieces = ImmutableArray.CreateBuilder<(Slot, int)>(count);
                for (int k = 0; k < count; k++) pieces.Add((new Slot(SlotKind.Integer, integers + k), Math.Min(slotBits, type.StorageBits - k * slotBits)));
                integers += count;
                return pieces.MoveToImmutable();
            }
            case AggregatePlacement.VectorPerMember:
                throw new Refuted(Verdict.MissingFact, $"同质浮点聚合体的{what}：放法已登记，语料里没有用例，尚未接入");
            case AggregatePlacement.Reference:
                throw new Refuted(Verdict.MissingFact, $"大于 {rules.MaximumInRegistersBytes} 字节的值类型{what}按引用传递，尚未接入");
            default:
                throw new Refuted(Verdict.MissingFact, $"值类型{what}的成员未知，传递方式不能判定");
        }
    }

    /// <summary>按调用约定取出一个值：各段依次是值的低位到高位，每段取所在槽位的低位。</summary>
    private Term Gather(ImmutableArray<(Slot Slot, int Bits)> pieces, Func<Slot, Term> value)
    {
        if (pieces.Length == 1) return terms.Slice(value(pieces[0].Slot), 0, pieces[0].Bits);
        var parts = new Term[pieces.Length];
        for (int i = 0; i < parts.Length; i++) parts[i] = terms.Slice(value(pieces[i].Slot), 0, pieces[i].Bits);
        return terms.Concat(parts);
    }

    private void Run()
    {
        var method = body.Method;
        var convention = Convention(method, out _);
        var env = ImmutableDictionary<Term, Term>.Empty;
        foreach (var parameter in template.EntryParameters)
        {
            var pieces = convention[parameter.Slot.Index];
            // 入口事实：C++ 的 bool 只取 0 与 1，值就是最低位（设计 7.7、16.2）。
            env = env.SetItem(parameter, method.Parameters[parameter.Slot.Index].TwoValued
                ? terms.ZeroExtend(terms.Slice(Entry(pieces[0].Slot), 0, 1), pieces[0].Bits) : Gather(pieces, Entry));
        }
        var conditions = PathConditions.Empty(terms);
        // 入口处成立的文字（设计 7.7）：实例方法的 this 非空；类型初始化器里所属类的初始化已触发。
        if (method.HasThis)
        {
            var self = Gather(convention[0], Entry);
            conditions = conditions.With(terms.Eq(self, terms.Zero(self.Width)), false)!;
        }
        if (body.InitializerOf is { } initialized) conditions = conditions.WithInitialized(initialized);
        var none = ImmutableDictionary<int, int>.Empty;
        Explore(new State(new Side(native.Entry, 0, ImmutableDictionary<Term, Term>.Empty, none), new Side(template.Entry, 0, env, none),
            conditions, Epoch: 1, Serial: 0, FrameGeneration: 0, [], [], ImmutableDictionary<long, Term>.Empty));
    }

    // ---- 推进 ----

    private void Step()
    {
        if (++steps > budget) throw new Refuted(Verdict.Budget, $"步数预算 {budget} 耗尽");
    }

    private void Explore(State state)
    {
        if (run is not null) { ExploreClaim(state); return; }
        if (leftTemplate is not null) { ExploreTemplates(state); return; }
        var onNative = Machine(ref state, inner: false);
        if (onNative.Kind == EventKind.Fork) { Fork(state, onNative, native: true); return; }
        var onTemplate = Template(ref state);
        if (onTemplate.Kind == EventKind.Vacuous) { paths++; return; }
        if (onTemplate.Kind == EventKind.Fork) { Fork(state, onTemplate, native: false); return; }
        Match(state, onNative, onTemplate);
    }

    private void Fork(State state, Event fork, bool native)
    {
        foreach (var (literals, next) in fork.Arms)
        {
            PathConditions? conditions = state.Conditions;
            foreach (var (condition, value) in literals)
            {
                if (!native && leftTemplate is null && Unnamed(condition) is { } attribute)
                    throw new Refuted(Verdict.MissingFact, $"模板的条件含现场尚未命名的运行时属性 {(RuntimeFunction)attribute.Attribute.Value}：{condition}");
                conditions = conditions?.With(condition, value);
                if (conditions is not null) conditions = Learn(conditions, condition, value);
            }
            if (conditions is null) continue;
            var forked = state with { Conditions = conditions };
            Explore(Place(forked, native ? Role.Native : forked.Inner is null ? Role.Template : Role.Inner, next));
        }
    }

    /// <summary>项里第一个规格登记、但还没有换成现场写法的运行时属性。</summary>
    private static Term? Unnamed(Term term)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        Term? Go(Term t)
        {
            if (t.Operands.Length == 0 || !seen.Add(t)) return null;
            if (t.Kind == TermKind.Attribute && t.Attribute.Value < KernelAttributes.Load) return t;
            foreach (var operand in t.Operands)
                if (Go(operand) is { } found) return found;
            return null;
        }
        return Go(term);
    }

    /// <summary>
    /// 原生代码的分支确立的单调事实（设计 7.4、14.5）：类的“初始化完成”标志非零的那条边之后，该类的初始化已触发。
    /// 标志按布局识别：类指针（类型实体）加登记的偏移上的读取。
    /// </summary>
    private PathConditions Learn(PathConditions conditions, Term condition, bool value)
    {
        while (condition.Kind == TermKind.Operation && condition.Op == Op.Not) { condition = condition.Operands[0]; value = !value; }
        var layout = facts.Layout;
        if (value || condition is not { Kind: TermKind.Operation, Op: Op.Eq } || !condition.Operands[1].IsZero) return conditions;
        if (condition.Operands[0] is { Kind: TermKind.Attribute } flag && flag.Attribute.Value == KernelAttributes.Load
            && flag.Width == layout.ClassInitializedBits
            && flag.Operands[0] is { Kind: TermKind.Operation, Op: Op.Add } address && address.Operands[0].Kind == TermKind.Entity
            && address.Operands[0].Entity.Kind == EntityKind.Type && address.Operands[1].IsConstant
            && address.Operands[1].Value == (UInt128)layout.ClassInitializedOffset)
            return conditions.WithInitialized(address.Operands[0].Entity);
        return conditions;
    }

    private Term Substitute(Term term, ImmutableDictionary<Term, Term> env, Dictionary<Term, Term> memo)
    {
        if (memo.TryGetValue(term, out var done)) return done;
        if (!env.TryGetValue(term, out var result))
        {
            result = term;
            if (term.Operands.Length > 0)
            {
                var parts = new Term[term.Operands.Length];
                bool changed = false;
                for (int i = 0; i < parts.Length; i++)
                {
                    parts[i] = Substitute(term.Operands[i], env, memo);
                    changed |= !ReferenceEquals(parts[i], term.Operands[i]);
                }
                if (changed) result = terms.Rebuild(term, parts);
            }
        }
        memo[term] = result;
        return result;
    }

    /// <summary>一行项在这一侧当前的取值：按环境代入，模板一侧把布局登记的属性换成现场的读取，再在路径条件下求值。</summary>
    private ImmutableArray<Term> Values(ImmutableArray<Term> row, Side side, ref State state, bool lower, bool foreign = false)
    {
        var memo = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        var substituted = new Term[row.Length];
        Dictionary<Term, Term>? native2 = null;
        int fresh = state.Fresh;
        for (int i = 0; i < row.Length; i++)
        {
            substituted[i] = foreign ? Import(row[i], side.Env, memo, ref fresh) : Substitute(row[i], side.Env, memo);
            // 声明的操作数是原生一侧的项：模板的形参换成它们之后，再按现场的环境取值。
            if (lower && run is not null) substituted[i] = Substitute(substituted[i], state.Native.Env, native2 ??= new(ReferenceEqualityComparer.Instance));
            if (lower) substituted[i] = Lower(substituted[i], ref state);
        }
        if (fresh != state.Fresh) state = state with { Fresh = fresh };
        var result = ImmutableArray.CreateBuilder<Term>(row.Length);
        foreach (var term in substituted) result.Add(state.Conditions.Evaluate(term));
        return result.MoveToImmutable();
    }

    private Term Value(Term term, Side side, ref State state, bool lower, bool foreign = false) => Values([term], side, ref state, lower, foreign)[0];

    /// <summary>
    /// 把被展开方法的快照里的项（属于另一个项池）换成本池的项：带标记的叶子按环境取值，常量与实体照值构造，
    /// 未定义占位的每一处换成一个新的任意值（设计 7.2）。
    /// </summary>
    private Term Import(Term term, ImmutableDictionary<Term, Term> env, Dictionary<Term, Term> memo, ref int fresh)
    {
        if (!term.HasUndefined && memo.TryGetValue(term, out var done)) return done;
        Term result;
        if (env.TryGetValue(term, out var bound)) result = bound;
        else if (term.Kind == TermKind.Undefined) result = terms.Arbitrary(2, default, 0, 0, fresh++, term.Width);
        else
        {
            var parts = new Term[term.Operands.Length];
            for (int i = 0; i < parts.Length; i++) parts[i] = Import(term.Operands[i], env, memo, ref fresh);
            result = terms.Transplant(term, parts);
        }
        if (!term.HasUndefined) memo[term] = result;
        return result;
    }

    private static State Place(State state, Role role, Side next) => role switch
    {
        Role.Native => state with { Native = next },
        Role.Inner => state with { Inner = state.Inner! with { Side = next } },
        _ => state with { Template = next },
    };

    /// <summary>
    /// 把模板里布局登记的运行时属性换成现场的读取（规格登记的等式，设计 7.8）：数组的长度是数组对象里固定偏移上的字，
    /// 运行时不可变，读取与历元无关。模板在数组上使用这个属性，说明该值是数组，这个位置由此登记为不可变。
    /// </summary>
    private Term Lower(Term term, ref State state)
    {
        var conditions = state.Conditions;
        var memo = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        Term Go(Term t)
        {
            if (t.Operands.Length == 0) return t;
            if (memo.TryGetValue(t, out var done)) return done;
            var parts = new Term[t.Operands.Length];
            bool changed = false;
            for (int i = 0; i < parts.Length; i++)
            {
                parts[i] = Go(t.Operands[i]);
                changed |= !ReferenceEquals(parts[i], t.Operands[i]);
            }
            Term result = changed ? terms.Rebuild(t, parts) : t;
            if (result.Kind == TermKind.Attribute && result.Attribute.Value == (int)RuntimeFunction.ArrayLength)
            {
                var layout = facts.Layout;
                var address = terms.Add(result.Operands[0], terms.Constant(layout.ArrayLengthOffset, layout.PointerBits));
                result = terms.Attribute(new AttributeId(KernelAttributes.Load), layout.ArrayLengthBits, address, terms.Zero(32));
                conditions = conditions.WithImmutable(address, layout.ArrayLengthBits).WithUpperBound(result, (UInt128)layout.ArrayLengthMaximum);
            }
            else if (result.Kind == TermKind.Attribute && result.Attribute.Value == (int)RuntimeFunction.ArrayLengthNative)
            {
                // 同一个长度字段按 il2cpp_array_size_t 读（指针位宽），取值范围相同。
                var layout = facts.Layout;
                var address = terms.Add(result.Operands[0], terms.Constant(layout.ArrayLengthOffset, layout.PointerBits));
                result = terms.Attribute(new AttributeId(KernelAttributes.Load), layout.PointerBits, address, terms.Zero(32));
                conditions = conditions.WithImmutable(address, layout.PointerBits).WithUpperBound(result, (UInt128)layout.ArrayLengthMaximum);
            }
            else if (result.Kind == TermKind.Attribute && result.Attribute.Value == (int)RuntimeFunction.FieldAddress && result.Operands[1].Kind == TermKind.Entity)
            {
                // 经地址取字段的地址：所属值的地址加字段在值里的偏移。
                result = terms.Add(result.Operands[0], terms.Constant(OffsetInValue(result.Operands[1].Entity), result.Width));
            }
            memo[t] = result;
            return result;
        }
        var lowered = Go(term);
        if (!ReferenceEquals(conditions, state.Conditions)) state = state with { Conditions = conditions };
        return lowered;
    }

    private Side Enter(IFlowGraph graph, Side side, Exit exit, ref State state, Role role)
    {
        var values = Values(exit.Arguments, side, ref state, lower: role == Role.Template, foreign: role == Role.Inner);
        var parameters = graph.Parameters(exit.Target);
        var env = side.Env;
        for (int i = 0; i < parameters.Length; i++) env = env.SetItem(parameters[i], values[i]);
        // 环上的切点配对与模拟不变式（设计 9.3）尚未实现：一条路径第二次进入同一个块时停下。
        int visits = side.Visits.GetValueOrDefault(exit.Target.Index) + 1;
        if (visits > 1) throw new Refuted(Verdict.Insufficient, "方法里有环：切点配对尚未实现") { Unsupported = true };
        return new Side(exit.Target, 0, env, side.Visits.SetItem(exit.Target.Index, visits));
    }

    /// <summary>块末的终结：能判定就前进并返回空；不能判定的分支返回分叉；返回与陷阱返回事件。</summary>
    private Event? Leave(IFlowGraph graph, ref State state, Role role)
    {
        var side = role switch { Role.Native => state.Native, Role.Inner => state.Inner!.Side, _ => state.Template };
        bool lower = role == Role.Template, foreign = role == Role.Inner;
        var terminator = graph.Terminator(side.Block);
        Side Go(Exit exit, ref State s)
        {
            if (exit.Kind != ExitKind.Target) throw new Refuted(Verdict.Insufficient, $"分支的一臂直接是 {exit.Kind}");
            return Enter(graph, side, exit, ref s, role);
        }
        void Advance(Side next, ref State s) => s = Place(s, role, next);
        switch (terminator.Kind)
        {
            case TerminatorKind.Invoke:
                throw new Refuted(Verdict.Insufficient, "带展开出口的调用：展开路径的对照尚未实现") { Unsupported = true };
            case TerminatorKind.Single:
            {
                var exit = terminator.Exits[0];
                switch (exit.Kind)
                {
                    case ExitKind.Target: Advance(Go(exit, ref state), ref state); return null;
                    case ExitKind.Return: return new Event(EventKind.Return) { Values = Values(exit.Arguments, side, ref state, lower, foreign) };
                    case ExitKind.Trap: return new Event(EventKind.Trap);
                    default: throw new Refuted(Verdict.MissingFact, "不返回的出口之前不是登记为不返回的调用");
                }
            }
            case TerminatorKind.Branch:
            {
                var condition = Value(terminator.Condition!, side, ref state, lower, foreign);
                if (state.Conditions.Decide(condition) is bool taken)
                {
                    Advance(Go(terminator.Exits[taken ? 0 : 1], ref state), ref state);
                    if (run is not null && role == Role.Native) state = Decided(state, new EdgeId(side.Block, taken ? 0 : 1));
                    return null;
                }
                var forked = state;
                return new Event(EventKind.Fork)
                {
                    Arms = [([(condition, true)], Go(terminator.Exits[0], ref forked)), ([(condition, false)], Go(terminator.Exits[1], ref forked))],
                };
            }
            default:
            {
                var selector = Value(terminator.Condition!, side, ref state, lower, foreign);
                int last = terminator.Exits.Length - 1;
                if (selector.IsConstant)
                {
                    int chosen = selector.Value < (UInt128)last ? (int)selector.Value : last;
                    Advance(Go(terminator.Exits[chosen], ref state), ref state);
                    if (run is not null && role == Role.Native) state = Decided(state, new EdgeId(side.Block, chosen));
                    return null;
                }
                var arms = ImmutableArray.CreateBuilder<(ImmutableArray<(Term, bool)>, Side)>(last + 1);
                var others = ImmutableArray.CreateBuilder<(Term, bool)>(last);
                var forked = state;
                for (int i = 0; i < last; i++)
                {
                    var equal = terms.Eq(selector, terms.Constant(i, selector.Width));
                    arms.Add(([(equal, true)], Go(terminator.Exits[i], ref forked)));
                    others.Add((equal, false));
                }
                arms.Add((others.ToImmutable(), Go(terminator.Exits[last], ref forked)));
                return new Event(EventKind.Fork) { Arms = arms.ToImmutable() };
            }
        }
    }

    // ---- 原生代码的一侧：现场，或模板一侧正在展开的被调方法 ----

    private Event Machine(ref State state, bool inner)
    {
        var role = inner ? Role.Inner : Role.Native;
        while (true)
        {
            Step();
            var snapshot = inner ? state.Inner!.Snapshot : native;
            IFlowGraph graph = inner ? snapshot : nativeGraph;
            var side = inner ? state.Inner!.Side : state.Native;
            if (run is not null && !inner && side.Block == run.Claim.Landing.Block && side.Index == run.Claim.Landing.Index)
                return new Event(EventKind.Landing);
            // 证明一条声明时，走进到不了落点的块就离开了它的窗口（被占用的边之后的只抛出尾除外）。
            if (run is not null && !inner && !run.Peeking && side.Index == 0 && !run.Reaching[side.Block.Index] && !state.Trail!.Tail)
                return new Event(EventKind.Departed);
            // 落点之前的路径经过环上的块：一次走查只代表第一次经过，后几次经过时的事实要靠切点处的归纳，尚未建立。
            if (run is not null && !inner && side.Index == 0 && run.Cyclic[side.Block.Index])
                throw new Refuted(Verdict.Insufficient, $"通往落点的路径经过环上的块 B{side.Block.Index}：环的处理（切点配对）尚未建立") { Unsupported = true };
            if (side.Index >= graph.OccurrenceCount(side.Block))
            {
                if (Leave(graph, ref state, role) is { } departed) return departed;
                continue;
            }
            var id = new OccurrenceId(side.Block, side.Index);
            var operands = Values(graph.Operands(id), side, ref state, lower: false, foreign: inner);
            var results = graph.Results(id);
            var env = side.Env;
            switch (snapshot[id])
            {
                case ReadOccurrence read:
                {
                    var value = MachineRead(ref state, inner, operands[0], read.Width);
                    env = env.SetItem(results[0], value);
                    if (run is not null && heapAccess) state = inner ? TemplateRead(state, value) : NativeRead(state, id, operands[0], read.Width, value);
                    break;
                }
                case WriteOccurrence:
                    MachineWrite(ref state, inner, operands[0], operands[1]);
                    if (run is not null && heapAccess && !inner) state = NativeWrite(state, id, operands[0], operands[1]);
                    break;
                case CallOccurrence call:
                {
                    if (call.Target is null) throw new Refuted(Verdict.MissingFact, $"原语调用 {call.Primitive} 没有登记");
                    if (!operands[0].IsConstant)
                        throw new Refuted(Verdict.MissingFact, call.ByJump
                            ? $"由跳转完成的调用：目标不是已知的函数入口（间接跳转的目标没有命名）：{operands[0]}"
                            : $"间接调用的目标没有命名：{operands[0]}");
                    ulong address = (ulong)operands[0].Value;
                    var callee = facts.Callee(address);
                    if (call.ByJump) JumpReturns(ref state, graph, snapshot, side, id, inner, callee);
                    var after = side with { Index = side.Index + 1 };
                    switch (callee.Kind)
                    {
                        case CalleeKind.Managed:
                            return new Event(EventKind.Call) { Address = address, Occurrence = id, Values = operands, After = after };
                        case CalleeKind.Runtime when callee.Operation!.Effect == RuntimeEffect.Throw:
                            // 登记为不返回：路径在此结束，其后的出现与出口不属于任何执行（设计 7.5）。
                            return new Event(EventKind.Throw) { Exception = callee.Operation.Exception };
                        case CalleeKind.Runtime when callee.Operation!.Effect == RuntimeEffect.ClassInitialize:
                        {
                            var initialized = Argument(call, operands, new Slot(SlotKind.Integer, 0));
                            if (!(state.Conditions.Evaluate(initialized) is { Kind: TermKind.Entity } named && state.Conditions.Initialized(named.Entity)))
                                return new Event(EventKind.Initialize) { Class = initialized, Occurrence = id, After = after };
                            // 幂等（设计 6.2）：该类的初始化已触发时，这次调用等于不执行。
                            for (int k = 0; k < results.Length; k++) env = env.SetItem(results[k], EventResult(state.Serial, k, results[k].Width));
                            state = state with { Serial = state.Serial + 1 };
                            break;
                        }
                        case CalleeKind.Runtime when callee.Operation!.Effect == RuntimeEffect.NewObject:
                            return new Event(EventKind.Allocate) { Class = Argument(call, operands, new Slot(SlotKind.Integer, 0)), Occurrence = id, After = after };
                        case CalleeKind.Runtime when callee.Operation!.Effect == RuntimeEffect.Unobservable:
                        {
                            // 结果登记为“实参所指的元数据槽的内容”时，类型的槽给出的是该类型的实体（与读这个槽相同）。
                            Term? content = callee.Operation.ReturnsSlot && Argument(call, operands, new Slot(SlotKind.Integer, 0)) is { IsConstant: true } slot
                                && facts.EntityAtSlot((ulong)slot.Value) is { } named ? terms.Entity(named, facts.Layout.PointerBits) : null;
                            for (int k = 0; k < results.Length; k++)
                                env = env.SetItem(results[k], content is not null && call.ResultSlots[k] == new Slot(SlotKind.Integer, 0) && results[k].Width == content.Width
                                    ? content : EventResult(state.Serial, k, results[k].Width));
                            state = state with { Serial = state.Serial + 1 };
                            break;
                        }
                        case CalleeKind.Runtime when callee.Operation!.Effect is RuntimeEffect.Pure or RuntimeEffect.MakeException:
                        {
                            // 没有内存效果的运行时操作：结果是登记的具名函数作用在实参上，或一个运行时构造的、种类已知的异常对象。
                            var operation = callee.Operation;
                            int pointerBits = facts.Layout.PointerBits;
                            Term value;
                            if (operation.Effect == RuntimeEffect.Pure)
                            {
                                var arguments = new Term[operation.Arguments];
                                for (int k = 0; k < arguments.Length; k++) arguments[k] = Argument(call, operands, new Slot(SlotKind.Integer, k));
                                value = terms.Attribute(new AttributeId((int)operation.Function), pointerBits, arguments);
                            }
                            else
                                value = terms.Attribute(new AttributeId(KernelAttributes.ExceptionObject), pointerBits,
                                    terms.Constant((int)operation.Exception, 32), terms.Constant(state.Serial, 32));
                            for (int k = 0; k < results.Length; k++)
                                env = env.SetItem(results[k], call.ResultSlots[k] == new Slot(SlotKind.Integer, 0) && results[k].Width == pointerBits
                                    ? value : EventResult(state.Serial, k, results[k].Width));
                            state = state with { Serial = state.Serial + 1 };
                            break;
                        }
                        case CalleeKind.Runtime when callee.Operation!.Effect == RuntimeEffect.ThrowArgument:
                        {
                            var thrown = Argument(call, operands, new Slot(SlotKind.Integer, 0));
                            // 抛出托管代码给出的异常对象：事件的操作数是这个对象。运行时构造的异常只比较种类（设计 16.2）。
                            if (thrown.Kind != TermKind.Attribute || thrown.Attribute.Value != KernelAttributes.ExceptionObject)
                                return new Event(EventKind.Throw) { Values = [thrown], Occurrence = id };
                            return new Event(EventKind.Throw) { Exception = (ExceptionKind)(int)thrown.Operands[0].Value };
                        }
                        default:
                            throw new Refuted(Verdict.MissingFact, $"未命名的调用：{callee.Name}");
                    }
                    break;
                }
                default:
                    throw new Refuted(Verdict.MissingFact, "动态栈分配的定位尚未实现");
            }
            state = Place(state, role, side with { Index = side.Index + 1, Env = env });
        }
    }

    /// <summary>
    /// 由跳转完成的调用读成“调用后返回”的两个前提（设计 7.1），不成立时这次调用是未命名的效果：
    /// 目标是函数入口——代码地图里的入口，或有命名依据的运行时函数；
    /// 返回行里的返回地址、栈指针与各保存寄存器等于入口处的值，与普通返回是同一个判断。
    /// 栈指针是否归位、返回地址留在寄存器里还是从栈上取回，都只是后一个判断的不同证明途径。
    /// </summary>
    private void JumpReturns(ref State state, IFlowGraph graph, MethodSnapshot snapshot, Side side, OccurrenceId id, bool inner, Callee callee)
    {
        if (callee.Kind == CalleeKind.Unknown)
            throw new Refuted(Verdict.MissingFact, $"由跳转完成的调用：目标 {callee.Name} 不是已知的函数入口");
        var row = graph.Terminator(side.Block).Exits[0].Arguments;
        for (int k = 0; k < snapshot.ReturnSlots.Length; k++)
        {
            var slot = snapshot.ReturnSlots[k];
            if (slot.Kind is not (SlotKind.ReturnAddress or SlotKind.StackPointer or SlotKind.Preserved)) continue;
            Term? expected = null;
            foreach (var parameter in snapshot.EntryParameters)
                if (parameter.Slot == slot) expected = inner ? side.Env.GetValueOrDefault(parameter) : parameter;
            // 这一格取自这次调用的结果时，它不是跳转那一刻的值。
            bool same = expected is not null && !MentionsResult(row[k], id)
                && state.Conditions.Same(Value(row[k], side, ref state, lower: false, foreign: inner), expected);
            if (!same)
                throw new Refuted(Verdict.MissingFact, $"由跳转完成的调用：返回行的 {slot} 不是入口处的值，不能读成调用后返回");
        }
    }

    private static bool MentionsResult(Term term, OccurrenceId occurrence)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        bool Go(Term t)
        {
            if (t.Kind == TermKind.Result) return t.Occurrence == occurrence;
            if (t.Operands.Length == 0 || !seen.Add(t)) return false;
            foreach (var operand in t.Operands)
                if (Go(operand)) return true;
            return false;
        }
        return Go(term);
    }

    private Term EventResult(int serial, int slot, int width) =>
        terms.Attribute(new AttributeId(KernelAttributes.EventResult), width, terms.Constant(serial, 32), terms.Constant(slot, 32));

    private static Term Argument(CallOccurrence call, ImmutableArray<Term> operands, Slot slot)
    {
        int index = call.ArgumentSlots.IndexOf(slot);
        if (index < 0) throw new Refuted(Verdict.Insufficient, $"调用没有给出实参槽 {slot}");
        return operands[index + 1];
    }

    private static long? FrameOffset(Term address, Term pointer)
    {
        if (ReferenceEquals(address, pointer)) return 0;
        if (address.Kind == TermKind.Operation && address.Op == Op.Add && ReferenceEquals(address.Operands[0], pointer) && address.Operands[1].IsConstant)
            return unchecked((long)(ulong)address.Operands[1].Value);
        return null;
    }

    private static bool MentionsStack(Term term, Term pointer)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        bool Go(Term t)
        {
            if (ReferenceEquals(t, pointer)) return true;
            if (t.Operands.Length == 0 || !seen.Add(t)) return false;
            foreach (var operand in t.Operands)
                if (Go(operand)) return true;
            return false;
        }
        return Go(term);
    }

    private Term MachineRead(ref State state, bool inner, Term address, int width)
    {
        heapAccess = false;
        var pointer = inner ? state.Inner!.StackPointer : stackPointer;
        if (FrameOffset(address, pointer) is long offset)
        {
            var frame = inner ? state.Inner!.Frame : state.Frame;
            if (frame.TryGetValue(offset, out var stored) && stored.Width >= width) return terms.Slice(stored, 0, width);
            foreach (var (at, value) in frame)
                if (at < offset + width / 8 && offset < at + value.Width / 8)
                    throw new Refuted(Verdict.MissingFact, $"帧上偏移 {offset} 处 {width} 位的读取与已有的写入部分重叠");
            return terms.Attribute(new AttributeId(KernelAttributes.FrameWord), width, terms.Constant(offset, 64),
                terms.Constant(inner ? state.Inner!.FrameGeneration : state.FrameGeneration, 32), terms.Constant(inner ? state.Inner!.Instance + 1 : 0, 32));
        }
        if (address.IsConstant && facts.InImageData((ulong)address.Value))
        {
            // 类型与字符串字面量的元数据槽：读取是该实体（类指针、字面量对象）。槽在被读取时已经初始化（设计 14.5、16.2）。
            if (width == facts.Layout.PointerBits && facts.EntityAtSlot((ulong)address.Value) is { } type) return terms.Entity(type, width);
            // 装入后只读的指针字（全局偏移表等）：值是链接期常量。
            if (width == facts.Layout.PointerBits && facts.LinkConstant((ulong)address.Value) is { } constant) return terms.Bits(constant, width);
            // 其余用途的元数据槽（类型句柄、方法、字段）：初始化之后不变，读取没有版本（设计 7.4）。
            if (width == facts.Layout.PointerBits && facts.MetadataSlot((ulong)address.Value))
                return terms.Attribute(new AttributeId(KernelAttributes.ImageWord), width, address, terms.Zero(32), terms.Zero(32));
            // 其余的字是运行时私有状态，可能被改写：读取的身份带上历元与序号，隔着事件、运行时调用或对数据区的写入的两次读取不视为同值。
            return terms.Attribute(new AttributeId(KernelAttributes.ImageWord), width, address, terms.Constant(state.Epoch, 32), terms.Constant(state.Serial, 32));
        }
        if (MentionsStack(address, pointer)) throw new Refuted(Verdict.MissingFact, $"地址由栈指针算出，但不是常量偏移：{address}");
        // 类结构上的读取（初始化完成标志、静态区指针）读的是运行时的数据，不是托管位置（设计 7.4）：它有读取的身份，但不是效果。
        heapAccess = !Facts.EffectGraph.OnClassStructure(address);
        return HeapRead(inner ? state.TemplateWrites : state.NativeWrites, address, width, state.Epoch);
    }

    private void MachineWrite(ref State state, bool inner, Term address, Term value)
    {
        heapAccess = false;
        var pointer = inner ? state.Inner!.StackPointer : stackPointer;
        if (FrameOffset(address, pointer) is long offset)
        {
            var before = inner ? state.Inner!.Frame : state.Frame;
            var frame = before;
            int generation = inner ? state.Inner!.FrameGeneration : state.FrameGeneration;
            foreach (var (at, old) in before)
                if (at != offset && at < offset + value.Width / 8 && offset < at + old.Width / 8) { frame = frame.Remove(at); generation++; }
            frame = frame.SetItem(offset, value);
            state = inner ? state with { Inner = state.Inner! with { Frame = frame, FrameGeneration = generation } }
                : state with { Frame = frame, FrameGeneration = generation };
            return;
        }
        // 映像数据区不是托管位置：初始化标志、元数据槽属于运行时私有状态，写入不可观察。
        if (address.IsConstant && facts.InImageData((ulong)address.Value))
        {
            state = state with { Serial = state.Serial + 1 };
            return;
        }
        if (MentionsStack(address, pointer)) throw new Refuted(Verdict.MissingFact, $"地址由栈指针算出，但不是常量偏移：{address}");
        if (MentionsStack(value, pointer)) throw new Refuted(Verdict.MissingFact, "帧地址被写入堆：帧对象逃逸");
        heapAccess = true;
        state = inner ? state with { TemplateWrites = Append(state.TemplateWrites, address, value, state.Epoch) }
            : state with { NativeWrites = Append(state.NativeWrites, address, value, state.Epoch) };
    }

    // ---- 堆：读取的身份与别名判定 ----

    private ImmutableList<Store> Append(ImmutableList<Store> writes, Term address, Term value, int epoch)
    {
        Term before = writes.Count > 0 ? writes[^1].Version : terms.Constant(epoch, 32);
        return writes.Add(new(address, value, terms.Attribute(new AttributeId(MemoryVersion), 1, before, address, value)));
    }

    /// <summary>
    /// 读取的身份：沿本侧自上一个事件以来的写入往回，位置相同的取被写的值，已证明不重叠的越过，
    /// 不能证明的停下——身份是（地址，那次写入之后的内存版本）。两侧做了同样的写入序列时版本相同。
    /// </summary>
    private Term HeapRead(ImmutableList<Store> writes, Term address, int width, int epoch)
    {
        for (int i = writes.Count - 1; i >= 0; i--)
        {
            var write = writes[i];
            if (ReferenceEquals(write.Address, address) && write.Value.Width == width) return write.Value;
            if (!Disjoint(write.Address, write.Value.Width, address, width))
                return terms.Attribute(new AttributeId(KernelAttributes.LoadAfter), width, address, write.Version);
        }
        return terms.Attribute(new AttributeId(KernelAttributes.Load), width, address, terms.Constant(epoch, 32));
    }

    /// <summary>别名判定（设计 7.4，只有这一处）：两段内存已证明不重叠。同一个基上常量偏移的两段按区间比较；其余不能判定。</summary>
    private static bool Disjoint(Term a, int aBits, Term b, int bBits)
    {
        static (Term? Base, Int128 Offset) Split(Term t)
        {
            if (t.IsConstant) return (null, (Int128)t.Value);
            if (t.Kind == TermKind.Operation && t.Op == Op.Add && t.Operands[1].IsConstant)
                return (t.Operands[0], unchecked((long)(ulong)t.Operands[1].Value));
            return (t, 0);
        }
        var (aBase, aOffset) = Split(a);
        var (bBase, bOffset) = Split(b);
        if (!ReferenceEquals(aBase, bBase)) return false;
        return aOffset + aBits / 8 <= bOffset || bOffset + bBits / 8 <= aOffset;
    }

    /// <summary>事件与结局处，双方写过的位置内容相同（写入归并，设计 6.2）。</summary>
    private void CompareWrites(State state)
    {
        if (run is not null) Synchronized(state);
        // 双方做了同一串写入（次序、位置、值都相同）：内存相同，不需要别名判定。
        if (state.NativeWrites.Count == state.TemplateWrites.Count)
        {
            bool identical = true;
            for (int i = 0; identical && i < state.NativeWrites.Count; i++)
            {
                var (mine, theirs) = (state.NativeWrites[i], state.TemplateWrites[i]);
                identical = mine.Value.Width == theirs.Value.Width && state.Conditions.Same(mine.Address, theirs.Address)
                    && state.Conditions.Same(mine.Value, theirs.Value);
            }
            if (identical) return;
        }
        Dictionary<(Term, int), Term> Final(ImmutableList<Store> writes, string which)
        {
            var map = new Dictionary<(Term, int), Term>();
            foreach (var write in writes)
            {
                foreach (var (address, width) in map.Keys)
                    if (!(ReferenceEquals(address, write.Address) && width == write.Value.Width) && !Disjoint(address, width, write.Address, write.Value.Width))
                        throw new Refuted(Verdict.MissingIndependence, $"{which}的两次写入不能证明不重叠：{address} 与 {write.Address}");
                map[(write.Address, write.Value.Width)] = write.Value;
            }
            return map;
        }
        var onNative = Final(state.NativeWrites, "现场");
        var onTemplate = Final(state.TemplateWrites, "模板");
        foreach (var (key, value) in onTemplate)
        {
            if (!onNative.TryGetValue(key, out var written))
                throw new Refuted(Verdict.Insufficient, $"模板写了 {key.Item1}（{key.Item2} 位），现场没有写");
            if (!state.Conditions.Same(written, value))
                throw new Refuted(Verdict.Insufficient, $"写入 {key.Item1} 的值不同：现场 {state.Conditions.Evaluate(written)}，模板 {state.Conditions.Evaluate(value)}");
        }
        foreach (var key in onNative.Keys)
            if (!onTemplate.ContainsKey(key)) throw new Refuted(Verdict.Insufficient, $"现场写了 {key.Item1}（{key.Item2} 位），模板没有写");
    }

    // ---- 模板一侧 ----

    private Term Locate(TemplateEffect effect, ReadOnlySpan<Term> @base, int bits, State state)
    {
        var layout = facts.Layout;
        switch (effect.Location)
        {
            case LocationKind.StaticField:
            {
                // 静态字段：所属类的静态区（类结构里的一个指针，按当前的内存读取）加字段的偏移。
                int offset = facts.StaticFieldOffset(effect.Entity!.Value)
                    ?? throw new Refuted(Verdict.MissingFact, $"静态字段 {effect.Entity} 的偏移未知");
                var owner = terms.Entity(effect.Owner!.Value, layout.PointerBits);
                var statics = HeapRead(state.TemplateWrites, terms.Add(owner, terms.Constant(layout.ClassStaticFieldsOffset, layout.PointerBits)),
                    layout.PointerBits, state.Epoch);
                return terms.Add(statics, terms.Constant(offset, layout.PointerBits));
            }
            case LocationKind.InstanceField:
            {
                int offset = facts.InstanceFieldOffset(effect.Entity!.Value)
                    ?? throw new Refuted(Verdict.MissingFact, $"字段 {effect.Entity} 的偏移未知");
                return terms.Add(@base[0], terms.Constant(offset, layout.PointerBits));
            }
            case LocationKind.FieldAtAddress:
                // 经地址访问的字段：所属值的地址加字段在值里的偏移。
                return terms.Add(@base[0], terms.Constant(OffsetInValue(effect.Entity!.Value), layout.PointerBits));
            case LocationKind.ArrayElement:
            {
                // 元素的地址：数组对象里数据的起点，加下标（按有符号数扩到指针位宽）乘元素的字节数。
                var index = terms.SignExtend(@base[1], layout.PointerBits);
                var data = terms.Add(@base[0], terms.Constant(layout.ArrayDataOffset, layout.PointerBits));
                return terms.Add(data, terms.Mul(index, terms.Constant(bits / 8, layout.PointerBits)));
            }
            default:
                throw new Refuted(Verdict.MissingFact, $"{effect.Location} 的位置尚未登记到布局");
        }
    }

    /// <summary>
    /// 值类型的实例字段在值里的字节偏移。经地址访问的字段都属于值类型：托管指针指向值类型的实例。
    /// 实例字段的偏移相对对象指针，值类型的字段按装箱之后的对象计（生成代码的偏移表写作 offsetof(T, f) + sizeof(RuntimeObject)），
    /// 在值里的偏移要减去对象头。
    /// </summary>
    private int OffsetInValue(EntityRef field)
    {
        int offset = facts.InstanceFieldOffset(field) ?? throw new Refuted(Verdict.MissingFact, $"字段 {field} 的偏移未知");
        int header = facts.Layout.ObjectHeaderBytes;
        return offset >= header ? offset - header : throw new Refuted(Verdict.MissingFact, $"字段 {field} 的偏移 {offset} 小于对象头，不是值类型的字段");
    }

    private Event Template(ref State state)
    {
        while (true)
        {
            if (state.Inner is not null)
            {
                // 正在展开一次调用：推进被调方法的快照。它返回时，结果按调用约定取出，模板从调用之后继续。
                var inside = Machine(ref state, inner: true);
                if (inside.Kind != EventKind.Return) return inside;
                var inner = state.Inner!;
                var resumed = inner.Continue;
                if (inner.Returned is { } returned)
                {
                    var value = Gather(returned, slot =>
                    {
                        int at = inner.Snapshot.ReturnSlots.IndexOf(slot);
                        return at >= 0 ? inside.Values[at] : throw new Refuted(Verdict.MissingFact, $"被展开方法的返回行没有槽位 {slot}");
                    });
                    resumed = resumed with { Env = resumed.Env.SetItem(inner.Result!, value) };
                }
                state = state with { Inner = null, Template = resumed };
                continue;
            }
            Step();
            var side = state.Template;
            if (side.Thrown != ExceptionKind.None) return new Event(EventKind.Throw) { Exception = side.Thrown };
            if (side.Index >= templateGraph.OccurrenceCount(side.Block))
            {
                if (Leave(templateGraph, ref state, Role.Template) is { } left) return left;
                continue;
            }
            var id = new OccurrenceId(side.Block, side.Index);
            var effect = template[id];
            var operands = Values(templateGraph.Operands(id), side, ref state, lower: true);
            var next = side with { Index = side.Index + 1 };
            switch (effect.Kind)
            {
                case EffectKind.ThrowIf:
                    switch (state.Conditions.Decide(operands[0]))
                    {
                        case true: return new Event(EventKind.Throw) { Exception = effect.Exception };
                        case false: break;
                        default:
                            return new Event(EventKind.Fork)
                            {
                                Arms = [([(operands[0], true)], side with { Thrown = effect.Exception }), ([(operands[0], false)], next)],
                            };
                    }
                    break;
                case EffectKind.Require:
                {
                    // 有定义条件（设计 9.1）：此后的对照只对条件成立的执行进行。
                    if (state.Conditions.Decide(operands[0]) == true) break;
                    if (state.Conditions.With(operands[0], true) is not { } assumed) return new Event(EventKind.Vacuous);
                    assumptions.Add($"{effect.Entry} 的有定义条件");
                    state = state with { Conditions = assumed };
                    break;
                }
                case EffectKind.Read:
                {
                    int width = effect.ResultWidths[0];
                    var address = Locate(effect, operands.AsSpan(), width, state);
                    var loaded = HeapRead(state.TemplateWrites, address, width, state.Epoch);
                    next = next with { Env = next.Env.SetItem(templateGraph.Results(id)[0], loaded) };
                    if (run is not null) state = TemplateRead(state, loaded);
                    break;
                }
                case EffectKind.Write:
                {
                    var value = operands[^1];
                    var address = Locate(effect, operands.AsSpan()[..^1], value.Width, state);
                    state = state with { TemplateWrites = Append(state.TemplateWrites, address, value, state.Epoch) };
                    break;
                }
                case EffectKind.Call:
                    return new Event(EventKind.Call) { Effect = effect, Occurrence = id, Values = operands, After = next };
                case EffectKind.ClassInitialize:
                    // 幂等（设计 6.2）：该类的初始化已触发时等于不执行。
                    if (state.Conditions.Initialized(effect.Entity!.Value)) break;
                    return new Event(EventKind.Initialize) { Effect = effect, Occurrence = id, After = next };
                case EffectKind.NewObject:
                    return new Event(EventKind.Allocate) { Effect = effect, Occurrence = id, After = next };
                case EffectKind.Throw:
                    // 抛出一个异常对象：事件的操作数是这个对象，路径在此结束。
                    return new Event(EventKind.Throw) { Effect = effect, Values = [operands[0]] };
                default:
                    throw new Refuted(Verdict.Insufficient, $"模板效果 {effect.Kind}（{effect.Function}）的对照尚未实现");
            }
            state = state with { Template = next };
        }
    }

    // ---- 事件的对照 ----

    private static Term? HiddenArgument(CallOccurrence call, Event reached, Slot slot, PathConditions conditions)
    {
        int index = call.ArgumentSlots.IndexOf(slot);
        return index < 0 ? null : conditions.Evaluate(reached.Values[index + 1]);
    }

    private static void CheckHiddenArgument(CallOccurrence call, Event reached, Slot slot, PathConditions conditions, EntityRef expected)
    {
        if (HiddenArgument(call, reached, slot, conditions) is not { Kind: TermKind.Entity } value)
            throw new Refuted(Verdict.MissingFact, $"共享入口的隐含实参 {slot} 未解析为实体，期望 {expected}");
        if (value.Entity != expected)
            throw new Refuted(Verdict.Insufficient, $"共享入口的隐含实参 {slot} 不同：实得 {value.Entity}，期望 {expected}");
    }

    private static string Name(Event e) => e.Kind switch
    {
        EventKind.Throw => e.Values.Length == 1 ? "抛出异常对象" : $"抛出 {e.Exception}",
        EventKind.Call => e.Effect is { } effect ? $"调用 {effect.Entity}" : $"调用 0x{e.Address:x}",
        EventKind.Return => "返回",
        EventKind.Initialize => "类初始化",
        EventKind.Allocate => "新对象",
        EventKind.Departed => "走进到不了落点的块",
        _ => e.Kind.ToString(),
    };

    private void Match(State state, Event onNative, Event onTemplate)
    {
        var conditions = state.Conditions;
        switch (onNative.Kind, onTemplate.Kind)
        {
            case (EventKind.Throw, EventKind.Throw) when onNative.Values.Length == 1 && onTemplate.Values.Length == 1:
                // 双方各抛出一个异常对象：同一个对象。
                if (!conditions.Same(onNative.Values[0], onTemplate.Values[0]))
                    throw new Refuted(Verdict.Insufficient,
                        $"抛出的异常对象不同：现场 {conditions.Evaluate(onNative.Values[0])}，模板 {conditions.Evaluate(onTemplate.Values[0])}");
                CompareWrites(state);
                paths++;
                return;
            case (EventKind.Throw, EventKind.Throw) when onNative.Values.Length == 0 && onTemplate.Values.Length == 0 && onNative.Exception == onTemplate.Exception:
                CompareWrites(state);
                paths++;
                return;
            case (EventKind.Landing, EventKind.Return):
                Landed(state);
                return;
            case (EventKind.Return, EventKind.Return):
            {
                // 返回行等于入口值：返回地址、栈指针、各保存寄存器（设计 7.1）。
                for (int k = 0; k < native.ReturnSlots.Length; k++)
                {
                    var slot = native.ReturnSlots[k];
                    if (slot.Kind is not (SlotKind.ReturnAddress or SlotKind.StackPointer or SlotKind.Preserved)) continue;
                    if (!conditions.Same(onNative.Values[k], Entry(slot)))
                        throw new Refuted(Verdict.Insufficient, $"返回行的 {slot} 不是入口处的值：{conditions.Evaluate(onNative.Values[k])}");
                }
                Convention(body.Method, out var result);
                if (result is { } returned)
                {
                    var value = Gather(returned, slot =>
                    {
                        int at = native.ReturnSlots.IndexOf(slot);
                        return at >= 0 ? onNative.Values[at] : throw new Refuted(Verdict.MissingFact, $"返回行没有槽位 {slot}");
                    });
                    if (!conditions.Same(value, onTemplate.Values[0]))
                        throw new Refuted(Verdict.Insufficient, $"返回值不同：现场 {conditions.Evaluate(value)}，模板 {conditions.Evaluate(onTemplate.Values[0])}");
                }
                CompareWrites(state);
                paths++;
                return;
            }
            case (EventKind.Call, EventKind.Call) when onTemplate.Effect is null:
            {
                // 模板一侧是被展开方法里的调用：同一个目标，按被调方法的签名逐个实参相同。
                if (onNative.Address != onTemplate.Address)
                    throw new Refuted(Verdict.Insufficient, $"调用的目标不同：现场 0x{onNative.Address:x}，被展开的方法里 0x{onTemplate.Address:x}");
                var callee = facts.Callee(onNative.Address);
                var inner = state.Inner!;
                var call = (CallOccurrence)native[onNative.Occurrence];
                var other = (CallOccurrence)inner.Snapshot[onTemplate.Occurrence];
                var shape = callee.MethodAtCall(slot => HiddenArgument(other, onTemplate, slot, conditions), out string reason)
                    ?? throw new Refuted(Verdict.MissingFact, reason);
                var convention = Convention(shape, out _);
                if (callee.SharedSignatures.HasValue)
                    CheckHiddenArgument(call, onNative, NativeEntryQueries.MethodArgumentSlot(convention), conditions, shape.Entity);
                for (int i = 0; i < convention.Length; i++)
                {
                    var given = Gather(convention[i], slot => Argument(call, onNative.Values, slot));
                    var expected = Gather(convention[i], slot => Argument(other, onTemplate.Values, slot));
                    if (!conditions.Same(given, expected))
                        throw new Refuted(Verdict.Insufficient,
                            $"第 {i} 个实参不同：现场 {conditions.Evaluate(given)}，被展开的方法里 {conditions.Evaluate(expected)}");
                    if (MentionsStack(given, stackPointer) || MentionsStack(expected, inner.StackPointer))
                        throw new Refuted(Verdict.MissingFact, "帧地址作为实参：帧对象逃逸");
                }
                CompareWrites(state);
                Explore(state with
                {
                    Native = onNative.After! with { Env = Bind(onNative.After.Env, nativeGraph.Results(onNative.Occurrence), call, null, state.Serial) },
                    Inner = inner with
                    {
                        Side = onTemplate.After! with { Env = Bind(onTemplate.After.Env, inner.Snapshot.Results(onTemplate.Occurrence), other, call, state.Serial) },
                    },
                    Epoch = state.Epoch + 1, Serial = state.Serial + 1, NativeWrites = [], TemplateWrites = [],
                });
                return;
            }
            case (EventKind.Call, EventKind.Call):
            {
                var effect = onTemplate.Effect!;
                if (effect.Indirect) throw new Refuted(Verdict.Insufficient, "间接调用的对照尚未实现");
                var method = effect.Entity!.Value;
                var generic = facts.GenericEntry(method);
                ulong entry = generic?.Address ?? facts.Entry(method) ?? throw new Refuted(Verdict.MissingFact, $"方法 {method} 的入口未知");
                if (entry != onNative.Address)
                {
                    Expand(state, onNative, onTemplate);
                    return;
                }
                var call = (CallOccurrence)native[onNative.Occurrence];
                var convention = Convention(effect.Signature!, out var result);
                var candidates = facts.Callee(entry).SharedSignatures;
                if (candidates.HasValue || generic is { MultipleEntities: true })
                {
                    var hidden = NativeEntryQueries.SharedMethodSlot(candidates ?? [], out string reason)
                        ?? throw new Refuted(Verdict.MissingFact, reason);
                    CheckHiddenArgument(call, onNative, hidden, conditions, method);
                }
                for (int i = 0; i < convention.Length; i++)
                {
                    var given = Gather(convention[i], slot => Argument(call, onNative.Values, slot));
                    if (!conditions.Same(given, onTemplate.Values[i]))
                        throw new Refuted(Verdict.Insufficient,
                            $"第 {i} 个实参不同：现场 {conditions.Evaluate(given)}，模板 {conditions.Evaluate(onTemplate.Values[i])}");
                    if (MentionsStack(given, stackPointer)) throw new Refuted(Verdict.MissingFact, "帧地址作为实参：帧对象逃逸");
                }
                CompareWrites(state);
                // 同一个事件：双方的结果相互绑定。此后是新的历元。
                var results = nativeGraph.Results(onNative.Occurrence);
                var nativeEnv = onNative.After!.Env;
                for (int k = 0; k < results.Length; k++) nativeEnv = nativeEnv.SetItem(results[k], EventResult(state.Serial, k, results[k].Width));
                var templateEnv = onTemplate.After!.Env;
                if (result is { } returned)
                {
                    int serial = state.Serial;
                    templateEnv = templateEnv.SetItem(templateGraph.Results(onTemplate.Occurrence)[0], Gather(returned, slot =>
                    {
                        int at = call.ResultSlots.IndexOf(slot);
                        return at >= 0 ? EventResult(serial, at, results[at].Width) : throw new Refuted(Verdict.MissingFact, $"调用的结果里没有槽位 {slot}");
                    }));
                }
                Explore(state with
                {
                    Native = onNative.After with { Env = nativeEnv }, Template = onTemplate.After with { Env = templateEnv },
                    Epoch = state.Epoch + 1, Serial = state.Serial + 1, NativeWrites = [], TemplateWrites = [],
                });
                return;
            }
            case (EventKind.Initialize, EventKind.Initialize):
            {
                // 同一个事件：现场的实参是被初始化的类的类指针。它返回之后该类的初始化已触发；类型初始化器可能改写堆，此后是新的历元。
                EntityRef type;
                if (onTemplate.Effect is { } declared) type = declared.Entity!.Value;
                else
                {
                    var expected = conditions.Evaluate(onTemplate.Class!);
                    if (expected.Kind != TermKind.Entity) throw new Refuted(Verdict.MissingFact, $"类初始化的实参不是已命名的类指针：{expected}");
                    type = expected.Entity;
                }
                var given = conditions.Evaluate(onNative.Class!);
                if (given.Kind != TermKind.Entity) throw new Refuted(Verdict.MissingFact, $"类初始化的实参不是已命名的类指针：{given}");
                if (given.Entity != type) throw new Refuted(Verdict.Insufficient, $"被初始化的类不同：现场 {given.Entity}，模板 {type}");
                CompareWrites(state);
                var results = nativeGraph.Results(onNative.Occurrence);
                var nativeEnv = onNative.After!.Env;
                for (int k = 0; k < results.Length; k++) nativeEnv = nativeEnv.SetItem(results[k], EventResult(state.Serial, k, results[k].Width));
                var next = state with
                {
                    Native = onNative.After with { Env = nativeEnv }, Conditions = conditions.WithInitialized(type),
                    Epoch = state.Epoch + 1, Serial = state.Serial + 1, NativeWrites = [], TemplateWrites = [],
                };
                if (onTemplate.Effect is not null) next = next with { Template = onTemplate.After! };
                else
                {
                    var inner = state.Inner!;
                    var other = (CallOccurrence)inner.Snapshot[onTemplate.Occurrence];
                    var call = (CallOccurrence)native[onNative.Occurrence];
                    next = next with
                    {
                        Inner = inner with
                        {
                            Side = onTemplate.After! with { Env = Bind(onTemplate.After.Env, inner.Snapshot.Results(onTemplate.Occurrence), other, call, state.Serial) },
                        },
                    };
                }
                Explore(next);
                return;
            }
            case (EventKind.Allocate, EventKind.Allocate):
            {
                // 新对象（设计 7.5）：同一个事件。现场的实参是被分配的类的类指针；模板的类是被构造的类，或被展开方法里同一个运行时操作的实参。
                // 之后双方的结果是同一个新引用，非空；分配含类初始化分量，该类的初始化已触发；类型初始化器可能改写堆，此后是新的历元。
                EntityRef type;
                if (onTemplate.Effect is { } declared) type = declared.Entity!.Value;
                else
                {
                    var expected = conditions.Evaluate(onTemplate.Class!);
                    if (expected.Kind != TermKind.Entity) throw new Refuted(Verdict.MissingFact, $"新对象的类不是已命名的类指针：{expected}");
                    type = expected.Entity;
                }
                var given = conditions.Evaluate(onNative.Class!);
                if (given.Kind != TermKind.Entity) throw new Refuted(Verdict.MissingFact, $"新对象的类不是已命名的类指针：{given}");
                if (given.Entity != type) throw new Refuted(Verdict.Insufficient, $"新对象的类不同：现场 {given.Entity}，模板 {type}");
                CompareWrites(state);
                var call = (CallOccurrence)native[onNative.Occurrence];
                int slot = call.ResultSlots.IndexOf(new Slot(SlotKind.Integer, 0));
                if (slot < 0) throw new Refuted(Verdict.MissingFact, "新对象的调用没有给出结果槽 Integer0");
                var results = nativeGraph.Results(onNative.Occurrence);
                var created = EventResult(state.Serial, slot, results[slot].Width);
                var next = state with
                {
                    Native = onNative.After! with { Env = Bind(onNative.After.Env, results, call, null, state.Serial) },
                    Conditions = conditions.WithInitialized(type).With(terms.Eq(created, terms.Zero(created.Width)), false)!,
                    Epoch = state.Epoch + 1, Serial = state.Serial + 1, NativeWrites = [], TemplateWrites = [],
                };
                if (onTemplate.Effect is not null)
                {
                    var result = templateGraph.Results(onTemplate.Occurrence)[0];
                    if (result.Width != created.Width) throw new Refuted(Verdict.MissingFact, $"新对象的结果是 {created.Width} 位，模板是 {result.Width} 位");
                    next = next with { Template = onTemplate.After! with { Env = onTemplate.After.Env.SetItem(result, created) } };
                }
                else
                {
                    var inner = state.Inner!;
                    var other = (CallOccurrence)inner.Snapshot[onTemplate.Occurrence];
                    next = next with
                    {
                        Inner = inner with
                        {
                            Side = onTemplate.After! with { Env = Bind(onTemplate.After.Env, inner.Snapshot.Results(onTemplate.Occurrence), other, call, state.Serial) },
                        },
                    };
                }
                Explore(next);
                return;
            }
            case (_, EventKind.Call) when onTemplate.Effect is { Indirect: false }:
                Expand(state, onNative, onTemplate);
                return;
            default:
                throw new Refuted(Verdict.Insufficient, $"事件不同：现场 {Name(onNative)}，模板 {Name(onTemplate)}");
        }
    }

    /// <summary>
    /// 一次对上的调用的各结果：按结果槽取同一个事件结果。reference 是对方的调用（结果按它的槽位次序编号）；
    /// 对方没有列出的槽位另取编号。
    /// </summary>
    private ImmutableDictionary<Term, Term> Bind(ImmutableDictionary<Term, Term> env, ImmutableArray<Term> results, CallOccurrence call,
        CallOccurrence? reference, int serial)
    {
        for (int k = 0; k < results.Length; k++)
        {
            int at = reference is null ? k : reference.ResultSlots.IndexOf(call.ResultSlots[k]);
            env = env.SetItem(results[k], EventResult(serial, at >= 0 ? at : 1000 + k, results[k].Width));
        }
        return env;
    }

    /// <summary>
    /// 展开（设计 9.2、14.2）：模板里的一次调用换成被调方法自己的原生效果图。现场在这里没有这次调用，
    /// 说明被调方法的代码已经并进了现场；被调方法的快照与它自己的 IL 等价是另一条凭据（9.4）。
    /// 入口槽位：实参按调用约定放在低位，槽位的其余位与别的槽位是这次展开独有的符号。
    /// </summary>
    private void Expand(State state, Event onNative, Event onTemplate)
    {
        var effect = onTemplate.Effect!;
        var method = effect.Entity!.Value;
        var generic = facts.GenericEntry(method);
        ulong entry = generic?.Address ?? facts.Entry(method) ?? throw new Refuted(Verdict.MissingFact, $"方法 {method} 的入口未知");
        var snapshot = snapshots?.Invoke(entry) ?? throw new Refuted(Verdict.MissingFact,
            $"事件不同：现场 {Name(onNative)}，模板 {Name(onTemplate)}；展开需要被调方法 0x{entry:x} 的快照，它没有快照");
        var convention = Convention(effect.Signature!, out var returned);
        Slot? hidden = generic is { MultipleEntities: true } ? NativeEntryQueries.MethodArgumentSlot(convention) : null;
        var env = ImmutableDictionary<Term, Term>.Empty;
        Term? pointer = null;
        foreach (var parameter in snapshot.EntryParameters)
        {
            var slot = parameter.Slot;
            var value = terms.Attribute(new AttributeId(KernelAttributes.InnerEntry), parameter.Width,
                terms.Constant(state.Inlines, 32), terms.Constant((int)slot.Kind, 32), terms.Constant(slot.Index, 32));
            if (slot == hidden) value = terms.Entity(method, parameter.Width);
            for (int i = 0; i < convention.Length; i++)
            {
                int offset = 0;
                foreach (var (at, bits) in convention[i])
                {
                    if (at == slot)
                    {
                        var whole = onTemplate.Values[i];
                        var given = offset == 0 && bits == whole.Width ? whole : terms.Slice(whole, offset, bits);
                        value = given.Width == parameter.Width ? given : terms.Concat(given, terms.Slice(value, given.Width, parameter.Width - given.Width));
                    }
                    offset += bits;
                }
            }
            if (slot.Kind == SlotKind.StackPointer) pointer = value;
            env = env.SetItem(parameter, value);
        }
        if (pointer is null) throw new Refuted(Verdict.MissingFact, "被展开方法的入口没有声明栈指针");
        var result = returned is null ? null : templateGraph.Results(onTemplate.Occurrence)[0];
        Explore(state with
        {
            Inner = new Inner(snapshot, new Side(snapshot.Entry, 0, env, ImmutableDictionary<int, int>.Empty), pointer, state.Inlines,
                ImmutableDictionary<long, Term>.Empty, 0, onTemplate.After!, result, returned),
            Inlines = state.Inlines + 1,
        });
    }
}
