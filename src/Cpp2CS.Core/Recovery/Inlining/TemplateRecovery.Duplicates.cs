using Cpp2CS.Ir;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 各路径出口不同：调用之后的代码被复制到了各路径（clang 的尾部复制与跳转线程化，以及路径拆分）。
/// 替换后只有一条路径的续接留下，它要在其他路径的状态上运行，所以必须与那条路径原来的续接等价。
/// 两边从各自的出口同步走：项表示成调用后的内存，返回值换成结果局部；可观察事件逐一对应，条件相同或相反的分支按对应的去向分别比较，
/// 目标块不同而后续相同也算相同；走到同一位置（活跃局部相同）、都返回或都抛出时结束。
/// </summary>
internal sealed partial class TemplateRecovery
{
    /// <summary>全部分叉的记录：走过的位置、其中可能抛出的位置和赋值过的局部。</summary>
    private sealed class TraceLog
    {
        public HashSet<(ulong Block, int Index)> Passed { get; } = [];
        public HashSet<(ulong Block, int Index)> Raising { get; } = [];
        public Dictionary<Variable, ManagedValue> Assigned { get; } = [];
        /// <summary>出口到第一个事件之间解引用的项：它们和出口复制的读取之间没有别的效果。</summary>
        public HashSet<ManagedValue>? FirstAccesses { get; set; }
    }

    /// <summary>出口之后一条路径的执行状态。分支时分叉，记录在分叉之间共用。</summary>
    private sealed class Trace
    {
        public required InlineEnd End { get; init; }
        public required Walker Walker { get; init; }
        public required TraceLog Log { get; init; }
        /// <summary>这一分叉上赋值过的局部。</summary>
        public HashSet<Variable> Assigned { get; init; } = [];
        /// <summary>这一分叉上新解引用的项。</summary>
        public HashSet<ManagedValue> Accessed { get; init; } = [];
        /// <summary>上一个事件以来解引用的项（已知非空的也算）。</summary>
        public HashSet<ManagedValue> Recent { get; init; } = [];
        public (ulong Block, int Index) Position => (Walker.Block, Walker.Index);
        public Trace Fork() => new() { End = End, Walker = Walker.Clone(), Log = Log, Assigned = [.. Assigned], Accessed = [.. Accessed], Recent = [.. Recent] };
    }

    /// <summary>一次比较的上下文。</summary>
    private sealed class DuplicateProof
    {
        public required InlineMatch Match { get; init; }
        public required ManagedBody Body { get; init; }
        public required IReadOnlyDictionary<ulong, ManagedBlock> Blocks { get; init; }
        /// <summary>取过地址的局部：可能经引用改变，不能只按环境比较。</summary>
        public required IReadOnlySet<Variable> Addressed { get; init; }
        public required IReadOnlyDictionary<Variable, LocalValue> LocalTypes { get; init; }
        /// <summary>只经整体赋值改变的结构体局部。</summary>
        public required IReadOnlySet<Variable> FrozenLocals { get; init; }
        /// <summary>汇合时总要核对的局部：区域内定义的和出口边复制的。</summary>
        public required IReadOnlySet<Variable> Tracked { get; init; }
        /// <summary>返回值在一条路径上的项（已表示成调用后的内存）与结果局部的对应。</summary>
        public required Func<InlineEnd, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)>> Pairs { get; init; }
        public HashSet<Variable> Verified { get; } = [];
        public int Budget { get; set; } = 4096;
        public string? Refusal { get; private set; }
        public bool Refuse(string reason)
        {
            Refusal ??= reason;
            return false;
        }
    }

    /// <summary>
    /// 依次试保留各路径的续接，优先经过调用最多、返回值不是常量的路径：那里的编译器已知事实最少，读取都还在，代码对其他路径也成立。
    /// 比较成立时其他路径的这段代码进入区域；它们定义的局部如果在区域外使用，由区域检查拒绝。
    /// </summary>
    private bool ConcludeDuplicated(InlineMatch match, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks, LocalValue? result,
        Func<InlineEnd, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)>> pairs)
    {
        var addressed = blocks.Values.SelectMany(b => b.Statements).SelectMany(ReadValues).SelectMany(ManagedValues.Walk)
            .OfType<AddressValue>().SelectMany(a => ManagedValues.Walk(a.Target)).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var localTypes = new Dictionary<Variable, LocalValue>();
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedAssignment assignment) localTypes[assignment.Target.Variable] = assignment.Target;
            if (statement is ManagedCall { Result: { } called }) localTypes[called.Variable] = called;
            foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies)) localTypes[copy.Target.Variable] = copy.Target;
        }
        var fieldStored = blocks.Values.SelectMany(b => b.Statements).OfType<ManagedStore>().Select(s => Root(s.Target)).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var frozen = localTypes.Keys.Where(v => !addressed.Contains(v) && !fieldStored.Contains(v) && types.Kind(localTypes[v].Type) == TypeKind.Struct).ToHashSet();
        var tracked = match.Locals.Keys.Concat(match.Ends.SelectMany(e => e.Copies).Select(c => c.Target.Variable)).ToHashSet();
        var current = new Dictionary<InlineEnd, IReadOnlyList<(ManagedValue, ManagedValue)>>(ReferenceEqualityComparer.Instance);
        IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> Pairs(InlineEnd end) =>
            current.TryGetValue(end, out var known) ? known : current[end] = pairs(end).Select(p => (Current(p.Actual, end), p.Carrier)).ToArray();
        string? refusal = null;
        foreach (var kept in match.Ends.OrderByDescending(e => e.Epoch).ThenBy(e => e.Result is ConstantValue ? 1 : 0).DistinctBy(e => e.Exit))
        {
            var proof = new DuplicateProof { Match = match, Body = body, Blocks = blocks, Addressed = addressed, FrozenLocals = frozen, LocalTypes = localTypes, Tracked = tracked, Pairs = Pairs };
            var retained = new TraceLog();
            var removed = match.Ends.Where(e => !ReferenceEquals(e, kept)).Select(e => (End: e, Log: new TraceLog())).ToArray();
            if (removed.All(other => SameOnward(BeginTrace(kept, proof, retained), BeginTrace(other.End, proof, other.Log), proof)))
                return Retain(match, proof, kept, retained, removed, result, pairs);
            refusal ??= proof.Refusal;
        }
        return match.Fail($"各路径在调用方的出口不同（{refusal}）：{string.Join(", ", match.Ends.Select(e => $"0x{e.Exit.Block:x}+{e.Exit.Index}"))}");
    }

    private bool Retain(InlineMatch match, DuplicateProof proof, InlineEnd kept, TraceLog retained, IReadOnlyList<(InlineEnd End, TraceLog Log)> removed, LocalValue? result,
        Func<InlineEnd, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)>> pairs)
    {
        var assigned = removed.SelectMany(r => r.Log.Assigned).ToArray();
        // 保留的代码在调用之后运行：它用到的、区域内定义的局部由返回值给出，或在调用之后重新读取。
        var used = false;
        var copies = new List<(LocalValue, ManagedValue)>();
        foreach (var variable in proof.Tracked.Concat(retained.Assigned.Keys).Concat(assigned.Select(a => a.Key)).Distinct().Where(kept.Env.ContainsKey))
        {
            if (!LiveAt(proof.Body, proof.Blocks, kept.Exit.Block, kept.Exit.Index, variable)) continue;
            var function = Current(Abstract(kept.Env[variable], pairs(kept), match), kept);
            var mentions = result is not null && Mentions(function, result);
            if (!mentions && !ReadsCurrent(function) && !match.Ends.SelectMany(e => e.Copies).Any(c => c.Target.Variable == variable)) continue;
            used |= mentions;
            copies.Add((proof.LocalTypes[variable], function));
        }
        // 出口复制在所有路径上都会求值：它重新读取时解引用的项，在其他路径上不能引入新的异常。
        foreach (var (_, function) in copies)
            foreach (var receiver in ReadReceivers(function))
                foreach (var (end, log) in removed)
                    if (!AccessKnownOn(receiver, end, log, proof))
                        return match.Fail($"各路径在调用方的出口不同（出口复制的解引用不同）：0x{end.Exit.Block:x}+{end.Exit.Index}");
        if (!used && !match.Ends.All(e => e.Result is null || NonThrowingInlineValue(e.Result)))
            return match.Fail("返回值没有承接的局部，且无法证明额外求值无副作用");
        match.Exit = kept.Exit;
        match.ExitCopies = copies;
        match.Result = used ? result : null;
        match.Forms.Add("duplicated");
        // 保留的代码不进入区域，即使另一条路径也走到了那里。
        match.Covered.UnionWith(removed.SelectMany(r => r.Log.Passed).Except(retained.Passed));
        match.Raising.UnionWith(removed.SelectMany(r => r.Log.Raising).Except(retained.Passed).Select(p => p.Block));
        foreach (var (variable, value) in assigned)
            if (!proof.Verified.Contains(variable) && !retained.Assigned.ContainsKey(variable))
            {
                match.Defined[variable] = value;
                match.Locals[variable] = proof.LocalTypes[variable];
            }
        return true;
    }

    private Trace BeginTrace(InlineEnd end, DuplicateProof proof, TraceLog log)
    {
        var state = end.State!;
        return new Trace
        {
            End = end,
            Log = log,
            Walker = new Walker
            {
                Blocks = proof.Blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Epoch = AfterRegion, Calls = 1 << 16,
                Visited = [end.Exit.Block],
                FrozenLocals = proof.FrozenLocals,
                Env = end.Env.ToDictionary(p => p.Key, p => Current(p.Value, end)),
                Assumptions = state.Assumptions.Select(a => (Current(a.Condition, end), a.Value)).ToList(),
                Dereferenced = state.Dereferenced.Select(d => Current(d, end)).ToHashSet(),
            },
        };
    }

    /// <summary>a 是保留的续接，b 是被它取代的续接：a 在 b 的状态上运行与 b 等价。</summary>
    private bool SameOnward(Trace a, Trace b, DuplicateProof proof)
    {
        for (var steps = 0; steps < 256; steps++)
        {
            if (!Settle(a, b, proof) || !Settle(b, a, proof)) return proof.Refuse("后续不能比较");
            b.Log.FirstAccesses ??= [.. b.Recent];
            if (a.Position == b.Position) return Joined(a, b, proof);
            if (--proof.Budget < 0) return proof.Refuse("后续不能比较");
            var (x, y) = (a.Walker.Current, b.Walker.Current);
            // 保留的条件在被取代路径的状态上已知时只走已知的一侧；被取代路径自身已知的条件同样不构成事件。
            if (Decided(x, a, b, proof) is { } retainedSide)
            {
                if (!Decide(a, retainedSide)) return proof.Refuse("后续不能比较");
                continue;
            }
            if (Decided(y, b, b, proof) is { } removedSide)
            {
                if (!Decide(b, removedSide)) return proof.Refuse("后续不能比较");
                continue;
            }
            switch (x, y)
            {
                case (ManagedStore p, ManagedStore q):
                    {
                        if (Location(a.Walker, p.Target) is not { } la || Term(a.Walker, p.Value) is not { } va
                            || Location(b.Walker, q.Target) is not { } lb || Term(b.Walker, q.Value) is not { } vb) return proof.Refuse("后续不能比较");
                        if (!Equal(la, a, lb, b, proof) || !Equal(va, a, vb, b, proof)) break;
                        Pass(a);
                        Pass(b);
                        a.Walker.Stores.Add((la, va));
                        b.Walker.Stores.Add((lb, vb));
                        a.Recent.Clear();
                        b.Recent.Clear();
                        a.Walker.Index++;
                        b.Walker.Index++;
                        continue;
                    }
                case (ManagedCall p, ManagedCall q) when p.Invocation.Method.Equals(q.Invocation.Method) && p.Invocation.Virtual == q.Invocation.Virtual:
                    {
                        var left = ManagedValues.Of(p.Invocation).Select(v => Term(a.Walker, v)).ToArray();
                        var right = ManagedValues.Of(q.Invocation).Select(v => Term(b.Walker, v)).ToArray();
                        if (left.Any(v => v is null) || right.Any(v => v is null)) return proof.Refuse("后续不能比较");
                        if (left.Length != right.Length || !SameHandlers(a, b, proof)
                            || !left.Zip(right).All(pair => Equal(pair.First!, a, pair.Second!, b, proof))) break;
                        Called(a, p);
                        Called(b, q);
                        continue;
                    }
                case (ManagedCheck p, ManagedCheck q) when p.Exception.Equals(q.Exception):
                    {
                        if (Term(a.Walker, p.Condition) is not { } ca || Term(b.Walker, q.Condition) is not { } cb) return proof.Refuse("后续不能比较");
                        if (!SameHandlers(a, b, proof) || !Equal(ca, a, cb, b, proof)) break;
                        Passed(a, ca);
                        Passed(b, cb);
                        continue;
                    }
                case (ManagedAssignment p, ManagedAssignment q):
                    {
                        if (Term(a.Walker, p.Value) is not { } va || Term(b.Walker, q.Value) is not { } vb) return proof.Refuse("后续不能比较");
                        if (!SameHandlers(a, b, proof) || !Equal(va, a, vb, b, proof)) break;
                        Assign(a, p, va);
                        Assign(b, q, vb);
                        continue;
                    }
                case (ManagedReturn p, ManagedReturn q) when (p.Value is null) == (q.Value is null):
                    {
                        if (p.Value is { } rp && q.Value is { } rq)
                        {
                            if (Term(a.Walker, rp) is not { } va || Term(b.Walker, rq) is not { } vb) return proof.Refuse("后续不能比较");
                            if (!Equal(va, a, vb, b, proof)) break;
                        }
                        Pass(a);
                        Pass(b);
                        return AccessesCovered(a, b, proof);
                    }
                case (ManagedThrow p, ManagedThrow q):
                    {
                        if (Term(a.Walker, p.Exception) is not { } va || Term(b.Walker, q.Exception) is not { } vb) return proof.Refuse("后续不能比较");
                        if (!SameHandlers(a, b, proof) || !Equal(va, a, vb, b, proof)) break;
                        Pass(a);
                        Pass(b);
                        return AccessesCovered(a, b, proof);
                    }
                case (ManagedBranch p, ManagedBranch q):
                    {
                        if (Term(a.Walker, p.Condition) is not { } ca || Term(b.Walker, q.Condition) is not { } cb) return proof.Refuse("后续不能比较");
                        bool crossed;
                        if (Equal(ca, a, cb, b, proof)) crossed = false;
                        else if (Equal(ca, a, Negate(cb), b, proof)) crossed = true;
                        else break;
                        Pass(a);
                        Pass(b);
                        var (aTaken, bTaken) = (a.Fork(), b.Fork());
                        aTaken.Walker.Assumptions.Add((ca, true));
                        a.Walker.Assumptions.Add((ca, false));
                        bTaken.Walker.Assumptions.Add((cb, true));
                        b.Walker.Assumptions.Add((cb, false));
                        if (!Along(aTaken, p.Taken) || !Along(a, p.Fallthrough) || !Along(bTaken, q.Taken) || !Along(b, q.Fallthrough)) return proof.Refuse("后续不能比较");
                        return crossed
                            ? SameOnward(aTaken, b, proof) && SameOnward(a, bTaken, proof)
                            : SameOnward(aTaken, bTaken, proof) && SameOnward(a, b, proof);
                    }
            }
            if (CheckAsBranch(a, b, proof) is { } absorbed)
            {
                if (!absorbed) return proof.Refuse("后续不能比较");
                continue;
            }
            // 被取代路径多出的判空：保留的代码不判空，靠这一段里的解引用抛出同样的异常。
            if (y is ManagedCheck extra && NullTested(extra, b.Walker) is { } tested && Term(b.Walker, extra.Condition) is { } condition
                && a.Recent.Concat(ImminentAccesses(a.Walker)).Any(accessed => Equal(accessed, a, tested, b, proof)))
            {
                Passed(b, condition);
                continue;
            }
            return proof.Refuse("后续不同");
        }
        return proof.Refuse("后续不能比较");
    }

    /// <summary>
    /// 检查的两种写法：一边是检查语句，另一边是条件分支，其中一侧只经跳转就抛出同一异常类型的新实例，抛出条件与检查条件相同。
    /// 两者在同样的条件下抛出同样的异常，否则都继续；clang 在不同路径上会选不同写法（判空分支与判空调用）。
    /// 不是这种形态时为 null；分支沿不抛出的一侧继续。
    /// </summary>
    private bool? CheckAsBranch(Trace a, Trace b, DuplicateProof proof)
    {
        var (x, y) = (a.Walker.Current, b.Walker.Current);
        var (checking, branching, check, branch) = (x, y) switch
        {
            (ManagedCheck c, ManagedBranch r) => (a, b, c, r),
            (ManagedBranch r, ManagedCheck c) => (b, a, c, r),
            _ => default,
        };
        if (check is null || branch is null || ThrowingSide(proof.Blocks, branch) is not { } side || !side.Exception.Equals(check.Exception)
            || side.Arrivals.Count > 0) return null;
        var throwsTaken = side.Taken;
        if (Term(checking.Walker, check.Condition) is not { } tested || Term(branching.Walker, branch.Condition) is not { } condition) return false;
        var raising = throwsTaken ? condition : Negate(condition);
        var same = ReferenceEquals(checking, a) ? Equal(tested, a, raising, b, proof) : Equal(raising, a, tested, b, proof);
        if (!same || !SameHandlers(a, b, proof)) return null;
        Passed(checking, tested);
        Pass(branching);
        branching.Walker.Assumptions.Add((condition, !throwsTaken));
        branching.Recent.Clear();
        return Along(branching, throwsTaken ? branch.Fallthrough : branch.Taken);
    }

    /// <summary>把一条路径走到下一个事件：读取和计算只改变环境，分配之类的求值是事件；途中到达对方的位置就停下。</summary>
    private bool Settle(Trace trace, Trace peer, DuplicateProof proof)
    {
        var walker = trace.Walker;
        for (var steps = 0; steps < 256; steps++)
        {
            if (trace.Position == peer.Position) return true;
            if (walker.Index >= walker.Blocks[walker.Block].Statements.Count) return false;
            switch (walker.Current)
            {
                case ManagedAssignment assignment:
                    if (Term(walker, assignment.Value) is not { } value) return false;
                    if (proof.Addressed.Contains(assignment.Target.Variable)
                        || ManagedValues.Walk(assignment.Value).OfType<LocalValue>().Any(l => proof.Addressed.Contains(l.Variable))) return false;
                    if ((ManagedEffects.Value(assignment.Value).Kinds & ~EffectKind.Read) != 0) return true;
                    Assign(trace, assignment, value);
                    break;
                case ManagedJump jump:
                    Pass(trace);
                    if (!Along(trace, jump.Edge)) return false;
                    break;
                default:
                    return true;
            }
        }
        return false;
    }

    /// <summary>经过当前语句：记下位置、可能抛出与新解引用的项。</summary>
    private void Pass(Trace trace)
    {
        var walker = trace.Walker;
        trace.Log.Passed.Add(trace.Position);
        if (Raises(walker, walker.Current)) trace.Log.Raising.Add(trace.Position);
        foreach (var value in ManagedValues.Of(walker.Current).Concat(ManagedValues.CopiedValues(walker.Current)).SelectMany(ManagedValues.Walk))
            if (Accessed(value) is { } receiver && Term(walker, receiver) is { } accessed)
            {
                trace.Recent.Add(accessed);
                if (walker.Dereferenced.Add(accessed)) trace.Accessed.Add(accessed);
            }
    }

    private void Assign(Trace trace, ManagedAssignment assignment, ManagedValue value)
    {
        Pass(trace);
        trace.Walker.Env[assignment.Target.Variable] = value;
        Assigned(trace, assignment.Target.Variable);
        trace.Walker.Index++;
    }

    private static void Assigned(Trace trace, Variable variable)
    {
        trace.Assigned.Add(variable);
        trace.Log.Assigned[variable] = trace.Walker.Env[variable];
    }

    private void Passed(Trace trace, ManagedValue condition)
    {
        Pass(trace);
        trace.Walker.Assumptions.Add((condition, false));
        trace.Recent.Clear();
        trace.Walker.Index++;
    }

    private void Called(Trace trace, ManagedCall call)
    {
        Pass(trace);
        var walker = trace.Walker;
        if (call.Result is { } result)
        {
            walker.Env[result.Variable] = new Returned(walker.Calls, result.Type, result.Width);
            Assigned(trace, result.Variable);
        }
        walker.Calls++;
        if (ManagedEffects.Invocation(call.Invocation).InvalidatesMemory)
        {
            walker.Epoch++;
            walker.Stores.Clear();
        }
        trace.Recent.Clear();
        walker.Index++;
    }

    private bool Along(Trace trace, ManagedEdge edge)
    {
        if (!Follow(trace.Walker, edge)) return false;
        foreach (var copy in edge.Copies) Assigned(trace, copy.Target.Variable);
        return true;
    }

    /// <summary>判定语句的结果在 on 的状态上已知时给出：检查已知不成立为假，分支为条件的值。</summary>
    private bool? Decided(ManagedStatement statement, Trace from, Trace on, DuplicateProof proof) => statement switch
    {
        ManagedBranch branch when Term(from.Walker, branch.Condition) is { } condition => KnownAcross(condition, from, on, proof),
        ManagedCheck check when Term(from.Walker, check.Condition) is { } condition && KnownAcross(condition, from, on, proof) == false => false,
        _ => null,
    };

    private bool Decide(Trace trace, bool side)
    {
        var walker = trace.Walker;
        if (walker.Current is ManagedCheck check)
        {
            Passed(trace, Term(walker, check.Condition)!);
            return true;
        }
        var branch = (ManagedBranch)walker.Current;
        Pass(trace);
        walker.Assumptions.Add((Term(walker, branch.Condition)!, side));
        return Along(trace, side ? branch.Taken : branch.Fallthrough);
    }

    /// <summary>项里的返回值换成结果局部，才能跨路径比较。</summary>
    private ManagedValue Normal(ManagedValue term, Trace trace, DuplicateProof proof) =>
        Canonical(Fold(Abstract(term, proof.Pairs(trace.End), proof.Match)));

    /// <summary>from 的项代入 on 的返回值：常量返回路径上它会折叠。</summary>
    private ManagedValue Transported(ManagedValue term, Trace from, Trace on, DuplicateProof proof) =>
        Canonical(Fold(Instantiate(Normal(term, from, proof), proof.Pairs(on.End))));

    private bool Equal(ManagedValue x, Trace a, ManagedValue y, Trace b, DuplicateProof proof) =>
        Same(x, a, y, b, proof) || Reloads(x, b, proof) is var reloaded && !ReferenceEquals(reloaded, x) && Same(reloaded, a, y, b, proof);

    private bool Same(ManagedValue x, Trace a, ManagedValue y, Trace b, DuplicateProof proof) =>
        SameTerm(Normal(x, a, proof), Normal(y, b, proof)) || SameTerm(Transported(x, a, b, proof), Canonical(Fold(y)));

    /// <summary>
    /// 保留路径（a）的项里调用之后对字段的重读，换成被取代路径（on）上仍持有区域之前所存字段值的局部：
    /// 按 <see cref="Reloaded"/>，保留的代码在 on 的状态上运行时这次重读得到的就是这个局部的值。没有可换的重读时返回原项。
    /// </summary>
    private ManagedValue Reloads(ManagedValue term, Trace on, DuplicateProof proof)
    {
        if (proof.Match.Available?.Value is not { } available) return term;
        var held = proof.Match.Held?.Value ?? [];
        ManagedValue Replace(ManagedValue value)
        {
            if (value is Observed { Read: FieldValue heldRead })
                foreach (var (location, stored) in held)
                    if (ReferenceEquals(heldRead.Field.Field, location.Field.Field) && SameTerm(heldRead.Receiver, location.Receiver) && heldRead.Width == location.Width
                        && on.End.Epoch == 0 && on.End.State is { } state && !state.Stores.Any(s => MayAlias(s.Location, location)))
                        return stored;
            if (value is Observed { Read: FieldValue })
                foreach (var variable in available.Keys)
                    if ((on.Walker.Env.GetValueOrDefault(variable) ?? proof.LocalTypes.GetValueOrDefault(variable)) is LocalValue saved
                        && saved.Variable == variable && Reloaded(saved, on, value, proof))
                        return saved;
            return MapTerm(value, Replace);
        }
        return Replace(term);
    }

    private bool? KnownAcross(ManagedValue condition, Trace from, Trace on, DuplicateProof proof) =>
        KnownCondition(ReferenceEquals(from, on) ? condition : Transported(Reloads(condition, on, proof), from, on, proof), on.Walker, NoBinding);

    private static bool SameHandlers(Trace a, Trace b, DuplicateProof proof) =>
        proof.Body.Regions.All(r => r.Try.Contains(a.Walker.Block) == r.Try.Contains(b.Walker.Block) && r.Handler.Contains(a.Walker.Block) == r.Handler.Contains(b.Walker.Block));

    /// <summary>走到同一位置：活跃的局部逐路径相同。一条路径重新求不变的值，另一条路径沿用区域之前保存的局部，也算相同。</summary>
    private bool Joined(Trace a, Trace b, DuplicateProof proof)
    {
        var match = proof.Match;
        bool Saved(ManagedValue x, ManagedValue y) => x is LocalValue saved && ImmutableValue(y)
            && SameCopyAt(proof.Body, proof.Blocks, match.Start.Block, match.Start.Index, saved.Variable, y);
        foreach (var variable in proof.Tracked.Concat(a.Assigned).Concat(b.Assigned).Distinct())
        {
            if (!LiveAt(proof.Body, proof.Blocks, a.Walker.Block, a.Walker.Index, variable)) continue;
            var local = proof.LocalTypes[variable];
            var first = a.Walker.Env.GetValueOrDefault(variable) ?? local;
            var second = b.Walker.Env.GetValueOrDefault(variable) ?? local;
            if (!Equal(first, a, second, b, proof) && !Saved(first, second) && !Saved(second, first) && !Reloaded(second, b, first, proof))
                return proof.Refuse($"汇合点的 {variable} 不同");
            proof.Verified.Add(variable);
        }
        return AccessesCovered(a, b, proof);
    }

    /// <summary>
    /// 保留的路径经过调用后重读字段，被取代的路径（on）沿用区域之前保存的局部：这条路径上内存没变过、也没写这个字段时，
    /// 保存的局部还是字段的内容。留下的重读在这条路径上得到相同的值，这正是编译器省掉它的依据。
    /// 反过来不成立：保留沿用局部的路径时重读被删，调用之后读到的是旧值。
    /// </summary>
    private bool Reloaded(ManagedValue saved, Trace on, ManagedValue reloaded, DuplicateProof proof)
    {
        if (saved is not LocalValue local || proof.Match.Available?.Value.GetValueOrDefault(local.Variable) is not { } known) return false;
        // 长度不可变，只要是同一个数组或字符串。
        if (known is ArrayLengthValue or StringLengthValue) return SameTerm(reloaded is Observed { Read: var length } ? length : reloaded, known);
        return known is FieldValue field && reloaded is Observed { Read: FieldValue read } && on.End.Epoch == 0
            && ReferenceEquals(read.Field.Field, field.Field.Field) && SameTerm(read.Receiver, field.Receiver)
            && on.End.State is { } state && !state.Stores.Any(s => MayAlias(s.Location, field));
    }

    /// <summary>项里读取时解引用的项（调用方的 this 除外）。</summary>
    private static List<ManagedValue> ReadReceivers(ManagedValue term)
    {
        var found = new List<ManagedValue>();
        void Visit(ManagedValue value)
        {
            if (Accessed(value) is { } receiver && receiver is not ArgumentValue { Index: -1 }) found.Add(receiver);
            MapTerm(value, child =>
            {
                Visit(child);
                return child;
            });
        }
        Visit(term);
        return found;
    }

    /// <summary>结果局部形式的项在这条路径的出口已知非空，或这条路径紧接着就解引用它。</summary>
    private bool AccessKnownOn(ManagedValue receiver, InlineEnd end, TraceLog log, DuplicateProof proof)
    {
        var start = BeginTrace(end, proof, new TraceLog());
        bool Same(ManagedValue accessed) => SameTerm(Normal(accessed, start, proof), receiver);
        if (start.Walker.Dereferenced.Any(Same) || (log.FirstAccesses?.Any(Same) ?? false)) return true;
        var moved = Canonical(Fold(Instantiate(receiver, proof.Pairs(end))));
        return KnownCondition(new ComparisonValue(Cond.Eq, moved, new ConstantValue(0, moved.Type, moved.Width), types.Boolean), start.Walker, NoBinding) == false;
    }

    /// <summary>保留的代码会在 b 的状态上执行：它多解引用的项在那里不能为空。</summary>
    private bool AccessesCovered(Trace a, Trace b, DuplicateProof proof)
    {
        foreach (var accessed in a.Accessed)
        {
            // this 不为空；区域之前读过字段、事实还在的接收者也不为空（否则那次读取就抛出了）。
            if (accessed is ArgumentValue { Index: -1 }
                || proof.Match.Available?.Value.Values.SelectMany(ManagedValues.Walk).OfType<FieldValue>().Any(f => SameTerm(f.Receiver, accessed)) == true) continue;
            var moved = Normal(accessed, a, proof);
            if (b.Walker.Dereferenced.Any(d => SameTerm(Normal(d, b, proof), moved))) continue;
            var nullTest = new ComparisonValue(Cond.Eq, accessed, new ConstantValue(0, accessed.Type, accessed.Width), types.Boolean);
            if (KnownAcross(nullTest, a, b, proof) != false) return proof.Refuse($"后续的解引用不同：{accessed}");
        }
        return true;
    }
}
