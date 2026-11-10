using Cpp2CS.Ir;
using System.Collections.Immutable;

namespace Cpp2CS.Recovery.Inlining;

internal enum JointMode { Discovery, Validation }

/// <summary>一条联合路径：两侧状态与共享的路径条件、事件序号。</summary>
internal sealed class JointPath
{
    public required SideState A { get; set; }
    public required SideState B { get; set; }
    public ImmutableList<Term> Phi { get; set; } = [];
    public int Serial { get; set; }
    /// <summary>复核中第一次在同一块入口未收敛的原因（之后继续执行，可能在更后面收敛）。</summary>
    public string? Divergence { get; set; }
    public JointPath Clone() => new() { A = A.Clone(), B = B.Clone(), Phi = Phi, Serial = Serial, Divergence = Divergence };
}

/// <summary>一条路径的结果；Vacuous 表示路径条件在绑定下自相矛盾，这条路径不存在。</summary>
internal sealed record PathOutcome(JointPath Path, string? Failure, bool Vacuous = false)
{
    public bool Success => Failure is null;
}

/// <summary>
/// 共同执行：两段程序在共享的 Φ 与 θ 下同步推进。每侧执行到下一个观察点；不可判定的分支与隐式抛出在 Φ 上分叉，
/// 两侧的分支不需要对齐；两侧都到事件时，事件必须同种、同身份、操作数相等，且此刻两侧的公共存储相等；
/// 一侧的调用与另一侧不对应时，调用在静态上唯一且有模板就展开为模板。
/// 发现模式中 A 是模板、B 是调用方，模板返回即结束（出口由发现过程选择）；复核模式中 A 是原方法体、B 是替换后的方法体，
/// 两侧在同一未改动的块入口状态相等，或同样返回、同样抛出即结束。
/// </summary>
internal sealed class Joint(Interpreter interpreter, Func<MethodRef, Program?> templates, JointMode mode)
{
    public int PathBudget { get; init; } = 256;
    public int UnfoldDepth { get; init; } = 5;
    /// <summary>发现：模板返回后，调用方的轨迹里是否已有出口。</summary>
    public Func<JointPath, bool>? Settled { get; init; }
    private Solver Solver => interpreter.Solver;
    private TermTable Terms => interpreter.Terms;

    /// <summary>入口的路径条件个数：入口事实不参与对齐，只有共同执行中两侧加入的文字参与。</summary>
    private int entryLiterals;

    public List<PathOutcome> Run(JointPath start, bool stopAtFailure)
    {
        entryLiterals = start.Phi.Count;
        var outcomes = new List<PathOutcome>();
        var stack = new Stack<JointPath>();
        stack.Push(start);
        var explored = 0;
        while (stack.TryPop(out var path))
        {
            if (++explored > PathBudget)
            {
                outcomes.Add(new(path, path.Divergence is { } divergence ? $"联合路径超过预算（{divergence}）" : "联合路径超过预算"));
                break;
            }
            if (Step(path, stack) is not { } outcome) continue;
            outcomes.Add(outcome);
            if (stopAtFailure && !outcome.Success) break;
        }
        return outcomes;
    }

    /// <summary>失败的路径若在当前绑定下不可行（绑定只增不减，之后仍不可行），这条路径不存在，不算失败。</summary>
    private PathOutcome Failed(JointPath path, string reason) => Solver.Infeasible(path.Phi) ? new(path, null, true)
        : new(path, path.Divergence is { } divergence ? $"{reason}（此前 {divergence}）" : reason);

    /// <summary>推进一条路径，直到结束（返回结果）或分叉（子路径压栈，返回 null）。</summary>
    private PathOutcome? Step(JointPath path, Stack<JointPath> stack)
    {
        while (true)
        {
            var a = interpreter.Advance(path.A, path.Phi);
            if (a.Kind == StopKind.Fail) return Failed(path, $"{Side(true)}：{a.Reason}");
            if (a.Kind == StopKind.Fork) { Fork(path, a.Alternatives!, stack); return null; }
            if (mode == JointMode.Discovery && a.Kind == StopKind.Return)
            {
                // 调用方推进到它的下一个观察点（事件、返回、抛出），续接窗口到此为止；途中的分支照常对齐、分叉。
                // 分叉之前轨迹里已有出口时不再分叉：区域止于最早的出口，之后的分支属于续接。
                var next = interpreter.Advance(path.B, path.Phi);
                if (next.Kind == StopKind.Fork && Settled?.Invoke(path) != true) { Fork(path, next.Alternatives!, stack); return null; }
                BindAtReturn(path, a.Value);
                return new(path, null);
            }
            var b = interpreter.Advance(path.B, path.Phi);
            if (b.Kind == StopKind.Fail) return Failed(path, $"{Side(false)}：{b.Reason}");
            if (b.Kind == StopKind.Fork) { Fork(path, b.Alternatives!, stack); return null; }
            if (mode == JointMode.Validation)
            {
                if (a.Kind == StopKind.Soft && b.Kind == StopKind.Soft)
                {
                    if (a.Block == b.Block)
                    {
                        if (Divergence(path, a.Block) is not { } divergence) return new(path, null);
                        path.Divergence ??= $"块 0x{a.Block:x}：{divergence}";
                    }
                    Resume(path.A, a.Block);
                    Resume(path.B, b.Block);
                    continue;
                }
                if (a.Kind == StopKind.Soft || b.Kind == StopKind.Soft)
                {
                    // 停在未改动块入口的一侧等另一侧：另一侧的事件能展开就先展开；否则两侧不在这里汇合，停着的一侧继续。
                    var waiting = a.Kind == StopKind.Soft;
                    var other = waiting ? b : a;
                    if (other.Kind == StopKind.Event && TryUnfoldOne(path, !waiting, other.Event!)) continue;
                    Resume(waiting ? path.A : path.B, (waiting ? a : b).Block);
                    continue;
                }
            }
            switch (a.Kind, b.Kind)
            {
                case (StopKind.Event, StopKind.Event):
                    if (Match(path, a.Event!, b.Event!) is { } mismatch)
                    {
                        if (TryUnfold(path, a.Event!, b.Event!)) continue;
                        return Failed(path, mismatch);
                    }
                    continue;
                case (StopKind.Event, _) when TryUnfoldOne(path, true, a.Event!):
                case (_, StopKind.Event) when TryUnfoldOne(path, false, b.Event!):
                    continue;
                case (StopKind.Throw, StopKind.Throw):
                    return SameThrow(path, a.Thrown!, b.Thrown!) is { } different ? Failed(path, different) : new(path, null);
                case (StopKind.Return, StopKind.Return):
                    return SameReturn(path, a.Value, b.Value) is { } different2 ? Failed(path, different2) : new(path, null);
                default:
                    return Failed(path, $"{Side(true)}的{Describe(a)}对应{Side(false)}的{Describe(b)}");
            }
        }
    }

    private string Side(bool a) => mode == JointMode.Discovery ? a ? "模板" : "调用方" : a ? "原方法体" : "替换后";

    private static string Describe(Stop stop) => stop.Kind switch
    {
        StopKind.Event => stop.Event!.Kind == EventKind.Call ? $"调用 {((MethodRef)stop.Event.Identity).Method.Name}" : $"{stop.Event.Kind}",
        StopKind.Throw => $"抛出 {stop.Thrown!.ExceptionType ?? "对象"}",
        StopKind.Return => "返回",
        StopKind.Soft => $"块 0x{stop.Block:x}",
        _ => stop.Kind.ToString(),
    };

    private static void Resume(SideState side, ulong block)
    {
        side.Resumed = block;
        side.Stop = null;
    }

    private void Fork(JointPath path, Term[] alternatives, Stack<JointPath> stack)
    {
        Align(path, alternatives);
        var children = new List<JointPath>();
        foreach (var literal in alternatives)
        {
            if (Solver.Decide(path.Phi, literal) == false) continue;
            var child = path.Clone();
            child.Phi = child.Phi.Add(literal);
            if (child.A.Stop?.Kind == StopKind.Fork) child.A.Stop = null;
            if (child.B.Stop?.Kind == StopKind.Fork) child.B.Stop = null;
            children.Add(child);
        }
        for (var i = children.Count - 1; i >= 0; i--) stack.Push(children[i]);
    }

    /// <summary>
    /// 两侧的同一个检查：分叉的条件与 Φ 中另一侧已有的文字只差未绑定的形参时，取使两者相同的绑定，这次分叉就由 Φ 判定。
    /// 从最近的文字开始找。绑定只是发现的选择，复核再确认。
    /// </summary>
    private void Align(JointPath path, Term[] alternatives)
    {
        if (mode != JointMode.Discovery) return;
        for (var i = path.Phi.Count - 1; i >= entryLiterals; i--)
        {
            var known = Solver.Apply(path.Phi[i]);
            foreach (var alternative in alternatives)
            {
                var candidate = Solver.Apply(alternative);
                if (known.HasFormal == candidate.HasFormal) continue;
                var (pattern, target) = known.HasFormal ? (known, candidate) : (candidate, known);
                var trial = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
                if (Solver.Match(pattern, target, trial) && trial.Count > 0)
                {
                    Solver.Bind(trial);
                    return;
                }
            }
        }
    }

    // ---- 事件 ----

    /// <summary>IL2CPP 对引用类型实参共享代码：同一方法定义、类型实参相同或同为引用类型。</summary>
    public static bool SharedCode(MethodRef a, MethodRef b) => a.Method == b.Method
        && a.TypeArguments.Count == b.TypeArguments.Count && a.MethodArguments.Count == b.MethodArguments.Count
        && a.TypeArguments.Zip(b.TypeArguments).All(p => SharedType(p.First, p.Second))
        && a.MethodArguments.Zip(b.MethodArguments).All(p => SharedType(p.First, p.Second));

    public static bool SharedType(TypeRef a, TypeRef b) => a.Equals(b) || ManagedTypes.IsReferenceType(a) && ManagedTypes.IsReferenceType(b)
        || a is ArrayRef x && b is ArrayRef y && x.Rank == y.Rank && SharedType(x.Element, y.Element);

    /// <summary>两个虚调用解析到继承链上同一个虚表槽。</summary>
    private static bool SameSlot(MethodDef a, MethodDef b)
    {
        if (!a.IsVirtual || !b.IsVirtual || a.Slot != b.Slot || a.Slot < 0) return false;
        static bool Derives(TypeDef type, TypeDef ancestor)
        {
            for (TypeDef? at = type; at is not null; at = (at.BaseType as DefinitionRef)?.Definition)
                if (ReferenceEquals(at, ancestor)) return true;
            return false;
        }
        return Derives(a.Owner, b.Owner) || Derives(b.Owner, a.Owner);
    }

    private static bool SameIdentity(EventInfo a, EventInfo b) => (a.Identity, b.Identity) switch
    {
        (MethodRef x, MethodRef y) => x.Equals(y) || SharedCode(x, y) || a.Virtual && b.Virtual && SameSlot(x.Method, y.Method),
        (TypeRef x, TypeRef y) => SharedType(x, y),
        (TypeDef x, TypeDef y) => ReferenceEquals(x, y),
        ((DefinitionRef dx, MethodRef mx, DelegateBinding bx), (DefinitionRef dy, MethodRef my, DelegateBinding by)) =>
            SharedType(dx, dy) && (mx.Equals(my) || SharedCode(mx, my)) && bx == by,
        _ => Equals(a.Identity, b.Identity),
    };

    /// <summary>两侧事件对应时完成它们；不对应时返回原因（不改变状态）。</summary>
    private string? Match(JointPath path, EventInfo a, EventInfo b)
    {
        if (a.Kind != b.Kind || !SameIdentity(a, b)) return $"{Describe(new Stop(StopKind.Event) { Event = a })} 对应 {Describe(new Stop(StopKind.Event) { Event = b })}";
        if (a.Identity is MethodRef method && method.Method.IsOverridable && a.Virtual != b.Virtual) return "调用的分派方式不同";
        if ((a.Receiver is null) != (b.Receiver is null) || a.Arguments.Length != b.Arguments.Length) return "事件的操作数个数不同";
        var trial = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        var pairs = a.Operands.Zip(b.Operands).ToArray();
        foreach (var (x, y) in pairs)
            if (!Solver.Match(Solver.Fold(path.Phi, x), Solver.Fold(path.Phi, y), trial)) return $"事件的操作数不同（{Solver.Apply(x)} 与 {y}）";
        // 比较失败时撤回绑定与逃逸：之后还可能改为展开调用。
        var binding = Solver.Snapshot();
        var saved = (path.A.Fresh, path.A.Exposed, path.B.Fresh, path.B.Exposed);
        if (trial.Count > 0) Solver.Bind(trial);
        foreach (var operand in a.Operands) interpreter.Escape(path.A, operand);
        foreach (var operand in b.Operands) interpreter.Escape(path.B, operand);
        if ((SameHeap(path, false) ?? SameContext(path)) is { } different)
        {
            Solver.Reset(binding);
            (path.A.Fresh, path.A.Exposed, path.B.Fresh, path.B.Exposed) = saved;
            return different;
        }
        var serial = ++path.Serial;
        var result = interpreter.Result(b.ResultType is not null ? b : a, serial);
        interpreter.Complete(path.A, a, result);
        interpreter.Complete(path.B, b, result);
        return null;
    }

    /// <summary>
    /// 可以展开的事件：从内联代码证明出的调用或构造（原生代码里本来就是被调方法的方法体），目标在静态上唯一且有模板。
    /// 原生代码里是调用指令的调用，在内联了外层方法的调用方中仍是调用，不展开。
    /// </summary>
    private Program? Unfoldable(SideState side, EventInfo evt)
    {
        if (side.Frames.Count > UnfoldDepth || !evt.Inlined) return null;
        if (evt.Kind == EventKind.Call && evt.Identity is MethodRef method)
        {
            if (method.Method.IsAbstract || evt.Virtual && method.Method.IsOverridable && !ExactReceiver(side, evt.Receiver)) return null;
            return templates(method);
        }
        if (evt.Kind == EventKind.Construct && evt.Identity is MethodRef constructor) return templates(constructor);
        return null;
    }

    /// <summary>接收者是本路径上分配的对象：运行时类型就是分配的类型，虚调用在静态上唯一。</summary>
    private bool ExactReceiver(SideState side, Term? receiver) => false;

    private bool Unfold(JointPath path, bool a, EventInfo evt)
    {
        var side = a ? path.A : path.B;
        if (Unfoldable(side, evt) is not { } template) return false;
        if (evt.Kind == EventKind.Construct) interpreter.BeginConstruct(side, template, evt);
        else interpreter.Unfold(side, template, evt, null);
        return true;
    }

    /// <summary>
    /// 两侧事件不对应时展开一侧的调用。复核时优先展开替换后的内联调用（就是要复核的那次调用），
    /// 发现时优先展开模板一侧（模板里的调用在调用方被内联了），再试另一侧。
    /// </summary>
    private bool TryUnfold(JointPath path, EventInfo a, EventInfo b)
    {
        var first = mode == JointMode.Validation ? false : true;
        if (mode == JointMode.Validation && path.B.Top.Program.Units[path.B.Top.Unit].Ops[path.B.Top.Op] is CallOp { Call.Inlined: true } && Unfold(path, false, b)) return true;
        return Unfold(path, first, first ? a : b) || Unfold(path, !first, first ? b : a);
    }

    /// <summary>一侧在事件、另一侧在结局：只能展开事件一侧。</summary>
    private bool TryUnfoldOne(JointPath path, bool a, EventInfo evt) => Unfold(path, a, evt);

    /// <summary>
    /// 模板返回时试探绑定仍未确定的形参：模板写过的位置与调用方的写入对应，返回值与调用方求过的值对应。
    /// 结构体返回值整体对应不上时逐个字段对应：调用方可以只取返回值的部分字段。
    /// 绑定只是一种选择，出口与复核再确认；其他路径（如判空分叉出的路径）因此可以判定。
    /// </summary>
    private void BindAtReturn(JointPath path, Term? returned)
    {
        SameHeap(path, false);
        if (returned is null || !Solver.Apply(returned).HasFormal) return;
        var candidates = path.B.Trace.SelectMany(p => p.Nodes.Values).Concat(path.B.Frames[0].Env.Values)
            .Where(c => !c.HasFormal && !c.IsConstant).Distinct(ReferenceEqualityComparer.Instance).Cast<Term>().Reverse().ToArray();
        var parts = returned.Kind == TermKind.Tuple ? [returned, .. returned.Args] : new[] { returned };
        foreach (var part in parts)
        {
            if (!Solver.Apply(part).HasFormal) continue;
            foreach (var candidate in candidates)
                if (Solver.Unify(part, candidate)) break;
        }
    }

    // ---- 堆与上下文 ----

    private IEnumerable<(Term Location, Term Value)> PublicWrites(SideState side) =>
        side.Writes.Where(w => !TermTable.Immutable(w.Location) && !interpreter.Private(side, w.Location));

    private Term? ReadAs(SideState side, Term location, Term like) =>
        interpreter.ReadScalar(side, location, new Leaf(FieldPath.Empty, like.Hint ?? interpreter.Types.Int32, like.Width, like.Bit), false);

    /// <summary>
    /// 两侧公共存储相等。发现时以模板的写入为准：每个写入在调用方有相同位置、相同值（调用方多出的写入留给区域规划）；
    /// 复核时两侧任一侧写过的位置内容都要相等。all 为真时比较全部存储（同步点）。
    /// </summary>
    private string? SameHeap(JointPath path, bool all)
    {
        if (path.A.Version != path.B.Version) return "堆版本不同";
        var a = (all ? path.A.Writes.Where(w => !CellOfFrame(w.Location)) : PublicWrites(path.A)).ToArray();
        var b = (all ? path.B.Writes.Where(w => !CellOfFrame(w.Location)) : PublicWrites(path.B)).ToArray();
        if (mode == JointMode.Discovery)
        {
            foreach (var (location, value) in a)
            {
                var applied = Solver.Fold(path.Phi, location);
                if (applied.HasFormal)
                {
                    var found = false;
                    // 经引用形参的写入可能落在调用方的私有单元（结构体局部）上：在调用方的全部写入里找。
                    foreach (var (other, otherValue) in path.B.Writes)
                    {
                        var trial = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
                        if (Solver.Match(applied, other, trial) && Solver.Match(Solver.Fold(path.Phi, value), Solver.Fold(path.Phi, otherValue), trial))
                        {
                            Solver.Bind(trial);
                            found = true;
                            break;
                        }
                    }
                    if (!found) return $"模板写入 {applied} 在调用方没有对应";
                    continue;
                }
                if (ReadAs(path.B, applied, value) is not { } actual) return $"调用方 {applied} 的内容不可判定";
                // 调用方没写过这个位置时，不用它的原内容去绑定未确定的形参：那只是一次空洞的猜测，θ 又在各路径间共享。
                if (Solver.Apply(value).HasFormal && actual.Kind == TermKind.Read && ReferenceEquals(actual.Location, applied)
                    && !path.B.Writes.Any(w => ReferenceEquals(w.Location, applied)))
                    return $"模板写入 {applied} 在调用方没有出现";
                if (!Solver.Unify(Solver.Fold(path.Phi, value), Solver.Fold(path.Phi, actual))) return $"写入不同（{applied}：{Solver.Apply(value)} 与 {actual}）";
            }
            return null;
        }
        foreach (var location in a.Select(w => w.Location).Concat(b.Select(w => w.Location)).Distinct(ReferenceEqualityComparer.Instance).Cast<Term>())
        {
            var like = a.Concat(b).First(w => ReferenceEquals(w.Location, location)).Value;
            var x = ReadAs(path.A, location, like);
            var y = ReadAs(path.B, location, like);
            if (x is null || y is null) return $"{location} 的内容不可判定";
            if (!ReferenceEquals(Solver.Fold(path.Phi, x), Solver.Fold(path.Phi, y))) return $"写入不同（{location}：{x} 与 {y}）";
        }
        return null;
    }

    /// <summary>展开帧的单元：帧结束后不可见。</summary>
    private static bool CellOfFrame(Term location) => location.Root == RootKind.Cell && location.Aux != 0;

    /// <summary>异常上下文：最内层 try 的处理块与其入口活跃局部的值。</summary>
    private (ulong? Handler, IReadOnlyDictionary<Variable, Term> Live) Context(SideState side)
    {
        if (side.OuterContext is { } outer) return outer;
        var bottom = side.Frames[0];
        var program = bottom.Program;
        var unit = program.Units[bottom.Unit];
        if (program.HandlerOf(unit.Source) is not { } region) return (null, new Dictionary<Variable, Term>());
        var live = new Dictionary<Variable, Term>();
        foreach (var variable in program.LiveIn(region.HandlerEntry))
        {
            if (region.Exception?.Variable.Equals(variable) == true) continue;
            if (bottom.Env.TryGetValue(variable, out var value)) live[variable] = value;
            else if (program.Cells.Contains(variable)) continue;
            else if (side.Entry is not null && Local(program, variable) is { } local) live[variable] = side.Entry(local);
        }
        return (region.HandlerEntry, live);
    }

    private static LocalValue? Local(Program program, Variable variable) => program.LocalOf(variable);

    /// <summary>可能抛出的事件处，两侧异常上下文相同；发现时只比较处理块（活跃局部由复核比较）。</summary>
    private string? SameContext(JointPath path)
    {
        var a = Context(path.A);
        var b = Context(path.B);
        if (a.Handler != b.Handler) return "异常处理上下文不同";
        if (mode == JointMode.Discovery || a.Handler is null) return null;
        foreach (var variable in a.Live.Keys.Union(b.Live.Keys))
            if (!a.Live.TryGetValue(variable, out var x) || !b.Live.TryGetValue(variable, out var y) || !ReferenceEquals(Solver.Fold(path.Phi, x), Solver.Fold(path.Phi, y)))
                return $"处理块入口活跃的 {variable} 不同";
        return null;
    }

    private string? SameThrow(JointPath path, ThrowInfo a, ThrowInfo b)
    {
        if (a.ExceptionType != b.ExceptionType) return $"抛出的异常不同（{a.ExceptionType ?? "对象"} 与 {b.ExceptionType ?? "对象"}）";
        if (a.Exception is not null && (b.Exception is null || !Solver.Unify(Solver.Fold(path.Phi, a.Exception), Solver.Fold(path.Phi, b.Exception)))) return "抛出的异常对象不同";
        if (a.Exception is not null) { interpreter.Escape(path.A, a.Exception); interpreter.Escape(path.B, b.Exception!); }
        return SameHeap(path, false) ?? SameContext(path);
    }

    private string? SameReturn(JointPath path, Term? a, Term? b)
    {
        if ((a is null) != (b is null)) return "返回值有无不同";
        if (a is not null && !Solver.Unify(Solver.Fold(path.Phi, a), Solver.Fold(path.Phi, b!))) return $"返回值不同（{a} 与 {b}）";
        if (a is not null) { interpreter.Escape(path.A, a); interpreter.Escape(path.B, b!); }
        return SameHeap(path, false);
    }

    /// <summary>复核的同步点：同一未改动的块入口，活跃局部与全部存储相等。</summary>
    /// <summary>两侧在同一未改动的块入口的差异：堆或活跃局部不同；相同时为 null。</summary>
    private string? Divergence(JointPath path, ulong block)
    {
        if (path.A.Frames.Count != 1 || path.B.Frames.Count != 1) return "仍在展开的调用中";
        if (SameHeap(path, true) is { } heap) return heap;
        var program = path.A.Frames[0].Program;
        foreach (var variable in program.LiveIn(block))
        {
            if (program.Cells.Contains(variable)) continue;
            var x = path.A.Frames[0].Env.GetValueOrDefault(variable);
            var y = path.B.Frames[0].Env.GetValueOrDefault(variable);
            if (x is null && y is null) continue;
            if (x is null || y is null)
            {
                var local = Local(program, variable) ?? Local(path.B.Frames[0].Program, variable);
                if (local is null || path.A.Entry is null) return $"活跃的 {variable} 只在一侧有值";
                x ??= path.A.Entry(local);
                y ??= path.B.Entry!(local);
            }
            if (!ReferenceEquals(Solver.Fold(path.Phi, x), Solver.Fold(path.Phi, y))) return $"活跃的 {variable} 不同（{x} 与 {y}）";
        }
        return null;
    }
}
