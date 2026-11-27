using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Independence;

namespace Cpp2CS.Kernel.Engine;

/// <summary>
/// 一条声明的证明（设计 9.3）。现场从方法入口走到落点；模板是声明的操作按目录展开的效果图，形参换成声明的操作数。
/// 现场每经过一个出现或一条边，按声明的占用分成两种：
///   被占用的——记下来，到下一个同步点（被占用的事件、被占用的抛出、落点）与模板在同一路径条件下产生的效果对照；
///   旁观的——在两侧都发生；它之前已有被占用的效果时，查独立关系（搬移）。
/// 路径条件由谁确立：声明自己占用的检查确立的条件不构成依赖；别的分支确立的条件被用到时，凭据把那个分支记为依赖。
/// 做法是证明两遍：第一遍只把自己占用的检查确立的条件并入路径条件，成立则没有依赖；否则第二遍并入全部条件，
/// 凭据把同步点之前经过的其他分支都记为依赖。
/// </summary>
public sealed partial class CoExecution
{
    /// <summary>路径上已经过的一个效果，供独立关系查询。</summary>
    internal sealed record Passed(EffectRef Effect, EffectClass Class, Term? Address, int Width, ExceptionKind Exception);

    /// <summary>
    /// 一条路径上与声明有关的记录。Entered：已经过被占用的效果（进了窗口）。Occupied：已经过的被占用效果。
    /// Deferred：与此前被占用的效果不能证明独立、因而要落在本声明之后的旁观效果。Reads 与 TemplateReads：
    /// 上一个同步点以来现场被占用的读取、模板做的读取。Tail：上一条分支边被占用，其后没有别的效果——接下来的抛出属于这条边。
    /// Excused：这条路径走进了一个被推后的旁观检查的只抛出尾。Outside：路径上确立了条件的、不属于本声明的分支。
    /// Consumed：这条路径经过了一个被消费的分支（设计 9.5），还没有到落点——输出里从那个分支直接接到落点，
    /// 所以其间不能有旁观效果，路径也不能从别处离开。
    /// </summary>
    internal sealed record Trail(bool Entered, ImmutableList<Passed> Occupied, ImmutableList<Passed> Deferred,
        ImmutableList<(Term Address, int Width, Term Value)> Reads, ImmutableList<Term> TemplateReads, int Epoch,
        bool Tail, bool Excused, ImmutableHashSet<BlockId> Outside)
    {
        public bool Consumed { get; init; }
    }

    private sealed class ClaimRun
    {
        public required Claim Claim;
        public required ClaimTemplate Template;
        public required bool OwnOnly;
        public readonly HashSet<OccurrenceId> Occurrences = [];
        public readonly HashSet<EdgeId> Edges = [];
        public readonly HashSet<BlockId> Terminators = [];
        public readonly HashSet<EffectRef> Touched = [], After = [];
        public readonly HashSet<BlockId> Before = [];
        public readonly SortedSet<string> Rows = new(StringComparer.Ordinal);
        /// <summary>能到达落点所在块的块；在环上的块。</summary>
        public required bool[] Reaching;
        public required bool[] Cyclic;
        public int Landings;
        public bool Peeking;
        /// <summary>被消费的分支所在的块；被占用的块末上、在某条路径上走过而没被占用的出口。</summary>
        public readonly HashSet<BlockId> Consumed = [];
        public readonly HashSet<EdgeId> Unoccupied = [];
    }

    private sealed class ClaimRefuted(Obligation obligation, string detail, string? row = null) : Exception(detail)
    {
        public Obligation Obligation => obligation;
        public string? Row => row;
    }

    private ClaimRun? run;

    internal static ImmutableArray<ImmutableArray<(Slot Slot, int Bits)>>? ConventionOrReason(MethodShape method,
        out ImmutableArray<(Slot Slot, int Bits)>? result, out string reason)
    {
        try
        {
            reason = "";
            return Convention(method, out result);
        }
        catch (Refuted refuted)
        {
            result = null;
            reason = refuted.Message;
            return null;
        }
    }

    internal static long? FrameOffsetOf(Term address, Term pointer) => FrameOffset(address, pointer);
    internal static bool MentionsStackPointer(Term term, Term pointer) => MentionsStack(term, pointer);

    /// <summary>证明一条声明。只由 <see cref="Proof.Prove"/> 调用。</summary>
    internal static ProofOutcome ProveClaim(RecoveryContext context, Claim claim, ClaimTemplate template, bool ownOnly, int budget)
    {
        var engine = new CoExecution(context.Snapshot, template.Graph, template.Body, context.Facts, context.Snapshots, budget);
        var snapshot = context.Snapshot;
        var reaching = new bool[snapshot.BlockCount];
        reaching[claim.Landing.Block.Index] = true;
        for (bool changed = true; changed;)
        {
            changed = false;
            for (int b = 0; b < reaching.Length; b++)
            {
                if (reaching[b]) continue;
                foreach (var exit in snapshot.Terminator(new BlockId(b)).Exits)
                    if (exit.Kind == ExitKind.Target && reaching[exit.Target.Index]) { reaching[b] = changed = true; break; }
            }
        }
        // 在环上的块：沿至少一条边能回到自己。
        var cyclic = new bool[reaching.Length];
        for (int b = 0; b < cyclic.Length; b++)
        {
            var seen = new bool[cyclic.Length];
            var pending = new Stack<int>();
            pending.Push(b);
            while (pending.Count > 0 && !cyclic[b])
                foreach (var exit in snapshot.Terminator(new BlockId(pending.Pop())).Exits)
                {
                    if (exit.Kind != ExitKind.Target) continue;
                    if (exit.Target.Index == b) cyclic[b] = true;
                    else if (!seen[exit.Target.Index]) { seen[exit.Target.Index] = true; pending.Push(exit.Target.Index); }
                }
        }
        var run = new ClaimRun { Claim = claim, Template = template, OwnOnly = ownOnly, Reaching = reaching, Cyclic = cyclic };
        foreach (var effect in claim.Occupied)
        {
            if (effect.IsEdge) { run.Edges.Add(effect.Edge); run.Terminators.Add(effect.Block); }
            else run.Occurrences.Add(effect.Occurrence);
        }
        engine.run = run;
        Refutation? refutation = null;
        try
        {
            engine.RunClaim(context);
            if (run.Landings == 0) throw new ClaimRefuted(Obligation.Coverage, "没有路径到达落点");
            foreach (var effect in claim.Occupied)
                if (!run.Touched.Contains(effect))
                    throw new ClaimRefuted(Obligation.Correspondence, $"占用的 {effect} 在任何路径上都没有作为这个操作的效果出现");
            // 被消费的分支不出现在输出里（设计 9.5）：它的每个走得到的出口都归这条声明。
            foreach (var edge in run.Unoccupied.OrderBy(e => e.Source.Index).ThenBy(e => e.Exit))
                if (run.Consumed.Contains(edge.Source))
                    throw new ClaimRefuted(Obligation.Correspondence, $"被消费的分支 B{edge.Source.Index} 的出口 {edge.Exit} 没有被占用");
        }
        catch (ClaimRefuted refuted)
        {
            refutation = new(RefutationLayer.Explanation, refuted.Obligation, refuted.Message, refuted.Row);
        }
        catch (Refuted refuted)
        {
            refutation = refuted.Verdict switch
            {
                Verdict.MissingFact => new(RefutationLayer.Fact, null, refuted.Message),
                Verdict.Budget => new(RefutationLayer.Budget, null, refuted.Message),
                Verdict.MissingIndependence => new(RefutationLayer.Explanation, Obligation.Correspondence, refuted.Message, "write-write"),
                _ when refuted.Unsupported => new(RefutationLayer.Engine, null, refuted.Message),
                _ => new(RefutationLayer.Explanation, Obligation.Correspondence, refuted.Message),
            };
        }
        ImmutableArray<string> rows = [.. run.Rows];
        if (refutation is not null) return new(claim, null, refutation, rows, engine.paths, engine.steps);
        var certificate = new Certificate(claim, context.Snapshot.DigestText, [.. run.Before.OrderBy(b => b.Index)], [.. run.After.Order()], rows,
            [.. engine.assumptions], template.OperandTypes, template.ResultType,
            template.Entry.Steps.Any(step => step.Location == LocationKind.ArrayElement) ? template.Entry.ImpliedBits : 0, engine.paths, engine.steps);
        return new(claim, certificate, null, rows, engine.paths, engine.steps);
    }

    private void RunClaim(RecoveryContext context)
    {
        var host = context.Host;
        var convention = Convention(host, out _);
        var env = ImmutableDictionary<Term, Term>.Empty;
        foreach (var parameter in template.EntryParameters) env = env.SetItem(parameter, run!.Claim.Operands[parameter.Slot.Index]);
        var conditions = PathConditions.Empty(terms);
        // 入口处成立的文字（设计 7.7）。
        if (host.HasThis)
        {
            var self = Gather(convention[0], Entry);
            conditions = conditions.With(terms.Eq(self, terms.Zero(self.Width)), false)!;
        }
        if (context.InitializerOf is { } initialized) conditions = conditions.WithInitialized(initialized);
        var none = ImmutableDictionary<int, int>.Empty;
        Explore(new State(new Side(native.Entry, 0, ImmutableDictionary<Term, Term>.Empty, none), new Side(template.Entry, 0, env, none),
            conditions, Epoch: 1, Serial: 0, FrameGeneration: 0, [], [], ImmutableDictionary<long, Term>.Empty)
        {
            Trail = new Trail(false, [], [], [], [], 1, false, false, []),
        });
    }

    private static EffectClass ClassOf(EventKind kind) => kind switch
    {
        EventKind.Call => EffectClass.Call,
        EventKind.Allocate => EffectClass.NewObject,
        _ => EffectClass.ClassInitialize,
    };

    private static string Where(State state) => $"B{state.Native.Block.Index}.{state.Native.Index}";

    private void ExploreClaim(State state)
    {
        var trail = state.Trail!;
        if (trail.Epoch != state.Epoch) state = state with { Trail = trail with { Epoch = state.Epoch, Reads = [], TemplateReads = [] } };
        var onNative = Machine(ref state, inner: false);
        trail = state.Trail!;
        switch (onNative.Kind)
        {
            case EventKind.Fork:
                ForkClaim(state, onNative);
                return;
            case EventKind.Landing:
                if (!trail.Entered && run!.Claim.Occupied.Length > 0)
                    throw new ClaimRefuted(Obligation.Coverage, "有一条路径到达落点而没有经过被占用的效果");
                Synchronize(state, onNative);
                return;
            case EventKind.Throw when onNative.Values.Length == 1 && run!.Occurrences.Contains(onNative.Occurrence):
                // 被占用的“抛出异常对象”：路径在这里结束，它就是这条路径上的落点。
                if (!run.Peeking) run.Landings++;
                Synchronize(Occupy(state, new Passed(EffectRef.Of(onNative.Occurrence), EffectClass.Call, null, 0, ExceptionKind.None)), onNative);
                return;
            case EventKind.Throw when trail.Tail && onNative.Values.Length == 0:
                Synchronize(state, onNative);
                return;
            case EventKind.Ended when state.Inner is { Side.Ended: true }:
                // 模板一侧正在展开的方法里是同一次不返回的调用：这个操作在这条路径上不返回，双方的词在那次调用处一同结束。
                Synchronized(state);
                paths++;
                return;
            case EventKind.Throw or EventKind.Return or EventKind.Trap or EventKind.Departed or EventKind.Ended:
                LeaveWindow(state, Name(onNative));
                return;
            default:
                if (run!.Occurrences.Contains(onNative.Occurrence))
                {
                    var passed = new Passed(EffectRef.Of(onNative.Occurrence), ClassOf(onNative.Kind), null, 0, ExceptionKind.None);
                    Synchronize(Occupy(state, passed), onNative);
                    return;
                }
                Explore(BystanderEvent(state, onNative));
                return;
        }
    }

    /// <summary>同步点：模板走到它的下一个事件，与现场的这个事件对照。模板的分支在路径条件下不能判定时分情况。</summary>
    private void Synchronize(State state, Event onNative)
    {
        var onTemplate = Template(ref state);
        // 登记不可变位置后路径条件自相矛盾，这条路径没有执行（设计 7.7）。
        if (state.Infeasible) { paths++; return; }
        // 声明是待证的一方：它的操作在现场走得到的路径上没有定义（有定义条件与路径条件矛盾），这条路径上的事件就没有对应（设计 9.1）。
        if (onTemplate.Kind == EventKind.Vacuous)
            throw new ClaimRefuted(Obligation.Correspondence, $"声明的操作在这条路径上没有定义：有定义条件与路径条件矛盾，现场的 {Name(onNative)} 没有对应");
        if (onTemplate.Kind == EventKind.Fork) { Fork(state, onTemplate, native: false); return; }
        Match(state, onNative, onTemplate);
    }

    /// <summary>每个同步点上：现场被占用的读取在模板里有对应；用到的路径条件由谁确立记进依赖。</summary>
    private void Synchronized(State state)
    {
        var trail = state.Trail!;
        foreach (var (address, width, value) in trail.Reads)
        {
            // 模板把这个位置当作运行时不可变数据使用（例如数组的长度）：这次读取是该属性的求值，不是托管位置上的读取。
            if (state.Conditions.IsImmutable(address, width)) continue;
            bool matched = false;
            foreach (var read in trail.TemplateReads) matched |= state.Conditions.Same(read, value);
            if (!matched) throw new ClaimRefuted(Obligation.Correspondence, $"被占用的读取 [{address}]（{width} 位）在模板里没有对应");
        }
        if (!run!.OwnOnly)
            foreach (var block in trail.Outside) run.Before.Add(block);
    }

    /// <summary>到达落点，模板也走完：结果是声明的定义；被推后的旁观效果记成落点约束。</summary>
    private void Landed(State state)
    {
        CompareWrites(state);
        var claim = run!.Claim;
        if (claim.Definition is { } definition)
        {
            var produced = state.Template.Env[run.Template.Result!];
            var claimed = Value(definition, state.Native, ref state, lower: false);
            if (!state.Conditions.Same(claimed, produced))
                throw new ClaimRefuted(Obligation.Correspondence, $"操作的结果不是声明的定义：模板 {state.Conditions.Evaluate(produced)}，定义 {claimed}");
        }
        foreach (var deferred in state.Trail!.Deferred) run.After.Add(deferred.Effect);
        run.Landings++;
        paths++;
    }

    /// <summary>独立关系的查询（设计 7.6）：按两种效果的种类取行，行的条件由内核按事实求值。查询过的行都记下来。</summary>
    private bool Independent(State state, Passed a, Passed b, out string row)
    {
        var entry = IndependenceTable.Find(a.Class, b.Class);
        row = entry?.Id ?? $"没有登记：{a.Class}、{b.Class}";
        if (!run!.Peeking) run.Rows.Add(row);
        if (entry is null) return false;
        return entry.Condition switch
        {
            IndependenceCondition.Always => true,
            IndependenceCondition.LocationsDisjoint =>
                Disjoint(state.Conditions.Evaluate(a.Address!), a.Width, state.Conditions.Evaluate(b.Address!), b.Width),
            // 去向相同由“去向”一项义务保证：方法里没有展开出口时，抛出都去往调用者。
            IndependenceCondition.SameException => a.Exception != ExceptionKind.None && a.Exception == b.Exception,
            _ => false,
        };
    }

    private State Occupy(State state, Passed passed)
    {
        var trail = state.Trail!;
        if (!run!.Peeking) run.Touched.Add(passed.Effect);
        if (trail.Occupied.Exists(p => p.Effect == passed.Effect)) return state;
        foreach (var deferred in trail.Deferred)
            if (!Independent(state, deferred, passed, out string row))
                throw new ClaimRefuted(Obligation.Motion,
                    $"旁观效果 {deferred.Effect}（{deferred.Class}）既不能越过此前被占用的效果，也不能越过其后被占用的 {passed.Effect}（{passed.Class}）", row);
        return state with { Trail = trail with { Entered = true, Occupied = trail.Occupied.Add(passed), Tail = trail.Tail && passed.Class == EffectClass.ConditionalThrow } };
    }

    /// <summary>
    /// 旁观效果（搬移）：它必须与此前被占用的效果独立。不独立而它自己没有内存效果时（读取、条件抛出），
    /// 可以改为要求它落在本声明之后（设计 9.4 的登记扩展）：记进 Deferred，此后被占用的效果都要与它独立。
    /// </summary>
    private State Bystander(State state, Passed passed)
    {
        if (state.Trail!.Consumed)
            throw new ClaimRefuted(Obligation.Motion, $"被消费的分支与落点之间有旁观效果 {passed.Effect}（{passed.Class}）：输出里这一段不存在");
        var trail = state.Trail! with { Tail = false };
        if (trail.Entered)
            foreach (var occupied in trail.Occupied)
            {
                if (Independent(state, occupied, passed, out string row)) continue;
                if (passed.Class is not (EffectClass.Read or EffectClass.ConditionalThrow))
                    throw new ClaimRefuted(Obligation.Motion,
                        $"被占用的 {occupied.Effect}（{occupied.Class}）与其后的旁观效果 {passed.Effect}（{passed.Class}）不能证明独立", row);
                if (!trail.Deferred.Exists(d => d.Effect == passed.Effect)) trail = trail with { Deferred = trail.Deferred.Add(passed) };
            }
        return state with { Trail = trail };
    }

    private State NativeRead(State state, OccurrenceId id, Term address, int width, Term value)
    {
        var passed = new Passed(EffectRef.Of(id), EffectClass.Read, address, width, ExceptionKind.None);
        if (!run!.Occurrences.Contains(id)) return Bystander(state, passed);
        state = Occupy(state, passed);
        return state with { Trail = state.Trail! with { Reads = state.Trail.Reads.Add((address, width, value)), Tail = false } };
    }

    private State NativeWrite(State state, OccurrenceId id, Term address, Term value)
    {
        var passed = new Passed(EffectRef.Of(id), EffectClass.Write, address, value.Width, ExceptionKind.None);
        if (run!.Occurrences.Contains(id))
        {
            state = Occupy(state, passed);
            return state with { Trail = state.Trail! with { Tail = false } };
        }
        // 旁观的写入在两侧都发生：输出里它排在这个操作之前。
        state = state with { TemplateWrites = Append(state.TemplateWrites, address, value, state.Epoch) };
        return Bystander(state, passed);
    }

    private State TemplateRead(State state, Term value) =>
        state with { Trail = state.Trail! with { TemplateReads = state.Trail.TemplateReads.Add(value) } };

    /// <summary>旁观的事件（调用、类初始化）：在两侧都发生，结果是同一个事件结果，此后是新的历元。</summary>
    private State BystanderEvent(State state, Event e)
    {
        var passed = new Passed(EffectRef.Of(e.Occurrence), ClassOf(e.Kind), null, 0, ExceptionKind.None);
        state = Bystander(state, passed);
        // 实参槽里的帧地址：帧对象逃逸给了被调方法。整数槽之外的槽位不携带地址实参。
        var call = (CallOccurrence)native[e.Occurrence];
        for (int i = 0; e.Kind == EventKind.Call && i < call.ArgumentSlots.Length; i++)
            if (call.ArgumentSlots[i].Kind == SlotKind.Integer && MentionsStack(e.Values[i + 1], stackPointer))
                throw new Refuted(Verdict.MissingFact, $"旁观的调用以帧地址作实参（{call.ArgumentSlots[i]}）：帧对象逃逸");
        var results = nativeGraph.Results(e.Occurrence);
        var env = e.After!.Env;
        for (int k = 0; k < results.Length; k++) env = env.SetItem(results[k], EventResult(state.Serial, k, results[k].Width));
        var conditions = state.Conditions;
        // 事件的后置条件：该类的初始化已触发（类初始化、新对象）；它由这个旁观效果确立，只在并入其他效果的条件的那一遍使用。
        if (e.Kind is EventKind.Initialize or EventKind.Allocate && !run!.OwnOnly && conditions.Evaluate(e.Class!) is { Kind: TermKind.Entity } named)
        {
            // 这个后置条件的确立者是这次事件：它所在的块记为依赖（9.4），占用它的声明不得落在本声明之后。
            conditions = conditions.WithInitialized(named.Entity);
            state = state with { Trail = state.Trail! with { Outside = state.Trail.Outside.Add(e.Occurrence.Block) } };
        }
        return state with
        {
            Native = e.After with { Env = env }, Conditions = conditions, Epoch = state.Epoch + 1, Serial = state.Serial + 1,
            NativeWrites = [], TemplateWrites = [],
        };
    }

    /// <summary>
    /// 现场的分支在路径条件下已经判定，state 已经在所走的那一臂上。走的那条边被占用时，其后的抛出属于它；
    /// 这一臂不是只抛出尾时，这个分支被消费（设计 9.5）。
    /// </summary>
    private State Decided(State state, EdgeId edge)
    {
        var trail = state.Trail!;
        if (!run!.Edges.Contains(edge))
        {
            if (!run.Peeking && run.Terminators.Contains(edge.Source)) run.Unoccupied.Add(edge);
            return state with { Trail = trail with { Tail = false, Excused = false } };
        }
        if (run.Peeking) return state with { Trail = trail with { Tail = true, Excused = false } };
        run.Touched.Add(EffectRef.Of(edge));
        bool consumed = Peek(state) == ExceptionKind.None;
        if (consumed) run.Consumed.Add(edge.Source);
        return state with { Trail = trail with { Entered = true, Tail = true, Excused = false, Consumed = trail.Consumed || consumed } };
    }

    /// <summary>这一臂是不是只抛出尾（设计 7.5）：沿它走到第一个事件，途中没有托管堆上的读写，事件是抛出。是则返回异常的种类。</summary>
    private ExceptionKind Peek(State arm)
    {
        var probe = arm with { Trail = arm.Trail! with { Entered = false, Occupied = [], Deferred = [], Tail = true, Consumed = false } };
        run!.Peeking = true;
        ExceptionKind kind = ExceptionKind.None;
        try
        {
            var first = Machine(ref probe, inner: false);
            if (first.Kind == EventKind.Throw && probe.Trail!.Tail) kind = first.Exception;
        }
        catch (Refuted)
        {
            // 这一臂上有读不懂的东西：它不是只抛出尾。随后正式走这一臂时同一个原因会再次出现并成为反驳。
        }
        run.Peeking = false;
        return kind;
    }

    private void ForkClaim(State state, Event fork)
    {
        var block = state.Native.Block;
        var before = state.Trail!;
        bool owned = run!.Terminators.Contains(block);
        if (!owned && before.Consumed)
            throw new ClaimRefuted(Obligation.Motion, $"被消费的分支与落点之间有旁观的分支 B{block.Index}：输出里这一段不存在");
        int count = fork.Arms.Length;
        var arms = new State?[count];
        var tails = new ExceptionKind[count];
        for (int i = 0; i < count; i++)
        {
            var (literals, next) = fork.Arms[i];
            PathConditions? conditions = state.Conditions;
            foreach (var (condition, value) in literals)
            {
                var narrowed = conditions?.With(condition, value);
                if (narrowed is not null) narrowed = Learn(narrowed, condition, value);
                // 第一遍只并入本声明占用的检查确立的条件；别的分支的条件只用来排除不可行的一臂。
                conditions = owned || !run.OwnOnly || narrowed is null ? narrowed : conditions;
            }
            if (conditions is null) continue;
            arms[i] = Place(state with { Conditions = conditions }, Role.Native, next);
            tails[i] = Peek(arms[i]!);
        }
        for (int i = 0; i < count; i++)
        {
            if (arms[i] is not { } arm) continue;
            var edge = new EdgeId(block, i);
            bool occupied = run.Edges.Contains(edge);
            // 被占用的边不通往只抛出尾：这个分支被消费（设计 9.5），它是操作内部的判断，不出现在输出里。
            bool consumed = occupied && tails[i] == ExceptionKind.None;
            if (occupied) run.Touched.Add(EffectRef.Of(edge));
            else if (owned) run.Unoccupied.Add(edge);
            if (consumed) run.Consumed.Add(block);
            // 这个分支其余各臂上的条件抛出，对走这一臂的执行来说是已经过的效果。
            for (int j = 0; j < count; j++)
            {
                if (j == i || tails[j] == ExceptionKind.None || arms[j] is null) continue;
                var check = new Passed(EffectRef.Of(new EdgeId(block, j)), EffectClass.ConditionalThrow, null, 0, tails[j]);
                arm = run.Edges.Contains(check.Effect.Edge) ? Occupy(arm, check) : Bystander(arm, check);
            }
            // 走进一个旁观检查的只抛出尾：这个检查若被推后（与此前被占用的效果不独立），输出里本声明的操作先于它执行。
            bool excused = false;
            if (!occupied && tails[i] != ExceptionKind.None && before.Entered)
            {
                var self = new Passed(EffectRef.Of(edge), EffectClass.ConditionalThrow, null, 0, tails[i]);
                foreach (var passed in before.Occupied) excused |= !Independent(state, passed, self, out _);
            }
            var trail = arm.Trail! with { Entered = arm.Trail.Entered || occupied, Tail = occupied, Excused = excused, Consumed = before.Consumed || consumed };
            if (!owned && !run.OwnOnly) trail = trail with { Outside = trail.Outside.Add(block) };
            Explore(arm with { Trail = trail });
        }
    }

    /// <summary>路径在落点之前结束（旁观的抛出、返回）：已经过的被占用效果必须可弃（设计 6.2、9.3 的搬移）。</summary>
    private void LeaveWindow(State state, string what)
    {
        var trail = state.Trail!;
        // 区域的各出口必须能归并（设计 9.5）。实现了第一种形式：经过被消费的分支的每条路径都到达落点这一个程序点。
        if (trail.Consumed)
            throw new ClaimRefuted(Obligation.Destination,
                $"经过被消费的分支的一条路径以“{what}”离开，没有到达落点：区域的出口不能归并（按结果分支、保留一份等价的后续这两种形式尚未实现）");
        if (trail.Entered && !trail.Excused)
            foreach (var occupied in trail.Occupied)
                if (occupied.Class is not (EffectClass.Read or EffectClass.ConditionalThrow))
                    throw new ClaimRefuted(Obligation.Motion, $"路径在落点之前以“{what}”结束，已经过的 {occupied.Effect}（{occupied.Class}）不可弃");
        paths++;
    }
}

/// <summary>事实层与引擎共用的几处判断：调用约定，帧上的常量偏移，地址是否由栈指针算出。各只有这一份实现。</summary>
internal static class EngineFacts
{
    public static ImmutableArray<ImmutableArray<(Slot Slot, int Bits)>>? Convention(MethodShape method,
        out ImmutableArray<(Slot Slot, int Bits)>? result, out string reason) => CoExecution.ConventionOrReason(method, out result, out reason);

    /// <summary>按调用约定取出一个值：各段依次是值的低位到高位，每段取所在槽位的低位。某个槽位没有给出时为空。</summary>
    public static Term? Gather(TermPool terms, ImmutableArray<(Slot Slot, int Bits)> pieces, Func<Slot, Term?> value)
    {
        var parts = new Term[pieces.Length];
        for (int i = 0; i < parts.Length; i++)
        {
            if (value(pieces[i].Slot) is not { } whole || whole.Width < pieces[i].Bits) return null;
            parts[i] = terms.Slice(whole, 0, pieces[i].Bits);
        }
        return parts.Length == 1 ? parts[0] : terms.Concat(parts);
    }
    public static long? FrameOffset(Term address, Term pointer) => CoExecution.FrameOffsetOf(address, pointer);
    public static bool MentionsStack(Term term, Term pointer) => CoExecution.MentionsStackPointer(term, pointer);
}
