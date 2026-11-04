using Cpp2CS.Ir;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 内联区域的出口。模板每条返回路径在调用方的终点由 <see cref="Finish"/> 求出：先纳入组成返回值的分段读取，再沿无条件跳转到达续接点。
/// 调用方在续接点观察到的值都是返回值的函数：对一条路径上的值把返回值抽象成结果局部，得到函数 f，再逐路径代入验证。
/// 布尔承接、零扩展、字段投影和比较都只是 f 的不同形式；条件续接的谓词同样如此，常量返回路径直接按谓词的取值选择续接。
/// 各路径的出口不同时，比较它们之后的代码：clang 常把调用之后的代码复制到各路径，相同就是同一个续接（<see cref="ConcludeDuplicated"/>）。
/// </summary>
internal sealed partial class TemplateRecovery
{
    private bool ConcludeExit(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks) =>
        ConcludeReturn(match, method) || ConcludeContinuation(match, method, body, blocks);

    /// <summary>模板的一条路径返回：调用方从当前位置沿无条件跳转到达的点是这条路径的出口，连同出口边上的复制记为一个终点。</summary>
    private bool Finish(Walker caller, InlineMatch match, ManagedValue? result)
    {
        if (result is not null && !CaptureReturnValue(caller, match, result)) return false;
        var copies = new List<(LocalValue, ManagedValue)>();
        var continuation = false;
        for (var steps = 0; steps < 16; steps++)
        {
            if (caller.Current is not (ManagedJump or ManagedAssignment)) break;
            // 共享续接保留赋值作为共同终点；跳转复制逐边组合，其他入边仍保留原块。
            continuation |= caller.Index == 0 && caller.Blocks.Values.Count(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == caller.Block)) > 1;
            if (!continuation && caller.Current is ManagedAssignment assignment && NonThrowingInlineValue(assignment.Value)
                && caller.Index == caller.Blocks[caller.Block].Statements.Count - 2
                && caller.Blocks[caller.Block].Statements[^1] is ManagedJump
                && caller.Env.TryGetValue(assignment.Target.Variable, out var previous)
                && Term(caller, assignment.Value) is { } assigned && SameTerm(previous, assigned))
            {
                var locals = ManagedValues.Walk(assignment.Value).OfType<LocalValue>().Select(l => l.Variable)
                    .Append(assignment.Target.Variable).ToHashSet();
                var addressed = caller.Blocks.Values.SelectMany(b => b.Statements).SelectMany(ReadValues).SelectMany(ManagedValues.Walk)
                    .OfType<AddressValue>().SelectMany(a => ManagedValues.Walk(a.Target)).OfType<LocalValue>().Any(l => locals.Contains(l.Variable));
                if (addressed) break;
                if (!continuation) Cover(caller, match);
                caller.Index++;
                continue;
            }
            if (caller.Current is not ManagedJump jump) break;
            if (continuation && jump.Edge.Copies.Any(c => !NonThrowingInlineValue(c.Value))) break;
            if (!continuation) Cover(caller, match);
            var edgeCopies = new List<(LocalValue Target, ManagedValue Value)>();
            foreach (var copy in jump.Edge.Copies)
            {
                if (Term(caller, copy.Value) is not { } value) return false;
                edgeCopies.Add((copy.Target, value));
            }
            foreach (var copy in edgeCopies) caller.Env[copy.Target.Variable] = copy.Value;
            copies.AddRange(edgeCopies);
            if (!caller.Blocks.ContainsKey(jump.Edge.Target)) return false;
            caller.Block = jump.Edge.Target;
            caller.Index = 0;
        }
        // 返回不分是否共享：共享的返回块不进入区域，调用之后写一条同样的返回。
        continuation |= caller.Index == 0 && caller.Blocks.Values.Count(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == caller.Block)) > 1;
        var returns = result is null && caller.Current is ManagedReturn { Value: null };
        if (result is not null && caller.Current is ManagedReturn { Value: { } returned }
            && Term(caller, returned) is { } actual)
        {
            var trial = new Dictionary<int, ManagedValue>(match.Binding);
            if (Unify(result, actual, trial))
            {
                foreach (var (key, value) in trial) match.Binding[key] = value;
                returns = true;
            }
        }
        if (returns && !continuation) Cover(caller, match);
        match.Ends.Add(new InlineEnd((caller.Block, caller.Index), copies, new Dictionary<Variable, ManagedValue>(caller.Env), result, returns, caller.Epoch) { State = caller.Clone() });
        return true;
    }

    /// <summary>返回表达式的读取可拆成若干赋值；只纳入结果本身及其读取子项，不越过无关求值。</summary>
    private bool CaptureReturnValue(Walker caller, InlineMatch match, ManagedValue result)
    {
        var terms = new List<ManagedValue>();
        void Collect(ManagedValue value)
        {
            if (value is Observed) terms.Add(value);
            MapTerm(value, child => { Collect(child); return child; });
        }
        Collect(result);
        if (terms.Count == 0) return true;
        for (var steps = 0; steps < 256; steps++)
        {
            if (caller.Index >= caller.Blocks[caller.Block].Statements.Count) return false;
            if (caller.Current is ManagedJump jump)
            {
                if (caller.Blocks.Values.Count(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == jump.Edge.Target)) > 1)
                    return true;
                Cover(caller, match);
                if (!Follow(caller, jump.Edge)) return false;
                continue;
            }
            if (caller.Current is not ManagedAssignment assignment || Term(caller, assignment.Value) is not { } value) return true;
            Dictionary<int, ManagedValue>? binding = null;
            var complete = false;
            foreach (var expected in new[] { result }.Concat(terms))
            {
                var trial = new Dictionary<int, ManagedValue>(match.Binding);
                if (!Unify(expected, value, trial)) continue;
                binding = trial;
                complete = ReferenceEquals(expected, result);
                break;
            }
            if (binding is null) return true;
            foreach (var (key, bound) in binding) match.Binding[key] = bound;
            Cover(caller, match);
            caller.Env[assignment.Target.Variable] = value;
            match.Defined[assignment.Target.Variable] = value;
            match.Locals[assignment.Target.Variable] = assignment.Target;
            caller.Index++;
            if (complete) return true;
        }
        return false;
    }

    /// <summary>返回：调用方在每条路径上直接返回模板的返回值（或都返回 void），返回类型可赋给调用方的返回类型。</summary>
    private bool ConcludeReturn(InlineMatch match, MethodRef method)
    {
        var returnedType = method.Concrete(method.Method.ReturnType);
        var callerReturn = caller.Concrete(caller.Method.ReturnType);
        if (match.Ends.Count == 0 || !match.Ends.All(e => e.Returns)
            || !returnedType.Equals(callerReturn) && !types.IsAssignable(returnedType, callerReturn)) return false;
        match.Exit = match.Ends[0].Exit;
        match.ExitCopies = [];
        match.Returns = true;
        match.Result = ManagedTypes.IsVoid(returnedType) ? null : NewLocal(returnedType);
        return true;
    }

    /// <summary>结果局部与它在某条路径上对应的项：返回值整体，以及结构体返回值的可访问叶子。</summary>
    private IEnumerable<(ManagedValue Actual, ManagedValue Carrier)> Carriers(InlineEnd end, TypeRef returnType, LocalValue result)
    {
        if (end.Result is not { } returned) yield break;
        yield return (returned, result);
        if (returnType is not DefinitionRef structure || types.Kind(structure) != TypeKind.Struct) yield break;
        foreach (var projection in types.Projections(structure))
        {
            ManagedValue carrier = result;
            var accessible = true;
            foreach (var field in projection.Path)
            {
                if (!fields.Accessible(field, carrier.Type)) { accessible = false; break; }
                var fieldType = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
                carrier = new FieldValue(carrier, field, fieldType, Width(fieldType));
            }
            if (accessible && ManagedProjections.Project(types, returned, projection, field => new Observed(field, end.Epoch)) is { Value: var value })
                yield return (value, carrier);
        }
    }

    /// <summary>项本身（不进入它的子项之外的结构）等于 part：字段投影的载体也算。</summary>
    private static bool Contains(ManagedValue value, ManagedValue part)
    {
        if (value.Equals(part)) return true;
        if (part is LocalValue && value is FieldValue) return false;
        var found = false;
        MapTerm(value, child =>
        {
            found |= Contains(child, part);
            return child;
        });
        return found;
    }

    private static bool Mentions(ManagedValue value, LocalValue local)
    {
        if (value is LocalValue found && found.Variable == local.Variable) return true;
        var mentioned = false;
        MapTerm(value, child =>
        {
            mentioned |= Mentions(child, local);
            return child;
        });
        return mentioned;
    }

    /// <summary>把项中等于返回值（或其叶子）的部分换成结果局部。</summary>
    private ManagedValue Abstract(ManagedValue value, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> carriers, InlineMatch match)
    {
        foreach (var (actual, carrier) in carriers)
        {
            if (actual is ConstantValue) continue;
            if (Unify(actual, value, new(match.Binding))) return carrier;
            // 布尔返回值的取反：调用方的条件常写成相反的比较。
            if (types.Kind(actual.Type) == TypeKind.Bool && Unify(Negate(actual), value, new(match.Binding)))
                return new ComparisonValue(Cond.Eq, carrier, new ConstantValue(0, carrier.Type, carrier.Width), types.Boolean);
        }
        return MapTerm(value, child => Abstract(child, carriers, match));
    }

    /// <summary>把结果局部代入这条路径的返回值，并折叠常量。</summary>
    private ManagedValue Instantiate(ManagedValue value, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> carriers)
    {
        foreach (var (actual, carrier) in carriers)
            if (carrier.Equals(value)) return actual;
        var mapped = MapTerm(value, child => Instantiate(child, carriers));
        return mapped switch
        {
            ComparisonValue { Left: ConstantValue left, Right: ConstantValue right } comparison when ConstantComparison(comparison.Condition, left, right) is { } truth
                => new ConstantValue(truth ? 1UL : 0UL, types.Boolean, 8),
            NegatedValue { Operand: ConstantValue operand } => new ConstantValue(operand.Bits == 0 ? 1UL : 0UL, types.Boolean, 8),
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: ConstantValue operand } conversion
                => new ConstantValue(operand.Bits & Expr.Mask(conversion.Width), conversion.Type, conversion.Width),
            _ => mapped,
        };
    }

    /// <summary>
    /// 续接：各路径或在同一点继续，或按返回值的谓词分到一对续接点。续接点活跃的局部都由结果局部的同一函数给出。
    /// 返回值没有被观察时可以丢弃，但模板额外求值的返回项不得引入异常或副作用。
    /// </summary>
    private bool ConcludeContinuation(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        if (match.Ends.Count == 0) return match.Fail("模板没有返回路径");
        var isVoid = ManagedTypes.IsVoid(method.Method.ReturnType);
        var returnType = method.Concrete(method.Method.ReturnType);
        if (!isVoid && match.Ends.Any(e => e.Result is null)) return match.Fail("返回路径没有返回值");
        var result = isVoid ? null : NewLocal(returnType);
        IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> Pairs(InlineEnd end) => result is null ? [] : Carriers(end, returnType, result).ToArray();
        Walker At(InlineEnd end) => new() { Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Env = new(end.Env), Epoch = end.Epoch };
        // 谓词取自一条在续接点按返回值分支的路径。
        ManagedValue? predicate = null;
        if (result is not null)
            foreach (var end in match.Ends.OrderBy(e => e.Result is ConstantValue ? 1 : 0))
            {
                if (At(end).Current is not ManagedBranch branch || Term(At(end), branch.Condition) is not { } tested) continue;
                var abstracted = Abstract(tested, Pairs(end), match);
                if (Mentions(abstracted, result)) { predicate = abstracted; break; }
            }
        var used = false;
        // 一个续接点的局部复制：逐路径验证同一函数。
        IReadOnlyList<(LocalValue Target, ManagedValue Value)>? Copies(IReadOnlyList<InlineEnd> ends)
        {
            var exit = ends[0].Exit;
            var edged = match.Covered.SelectMany(p => ManagedValues.Edges(blocks[p.Block].Statements[p.Index])).SelectMany(e => e.Copies).Select(c => c.Target)
                .Concat(ends.SelectMany(e => e.Copies.Select(c => c.Target))).DistinctBy(l => l.Variable).ToArray();
            var targets = edged.Concat(match.Locals.Values.Where(l => match.Defined.ContainsKey(l.Variable))).DistinctBy(l => l.Variable).ToArray();
            var copies = new List<(LocalValue, ManagedValue)>();
            foreach (var target in targets)
            {
                var held = ends.Select(e => e.Env.GetValueOrDefault(target.Variable) ?? target).ToArray();
                var isEdge = edged.Any(l => l.Variable == target.Variable);
                // 死的边复制可以丢弃，除非边上的求值本身可能抛出（只复制局部时不会，它的来源已经比对过）。
                var evaluated = match.Covered.SelectMany(p => ManagedValues.Edges(blocks[p.Block].Statements[p.Index])).SelectMany(e => e.Copies)
                    .Where(c => c.Target.Variable == target.Variable).Select(c => c.Value);
                if (!LiveAt(body, blocks, exit.Block, exit.Index, target.Variable) && (!isEdge || evaluated.All(NonThrowingInlineValue))) continue;
                var abstracted = Enumerable.Range(0, ends.Count).OrderBy(i => ends[i].Result is ConstantValue ? 1 : 0)
                    .Select(i => Abstract(held[i], Pairs(ends[i]), match)).First();
                // 与返回值无关的区域内定义由保存副本与区域外使用的检查处理。
                var mentioned = result is not null && Mentions(abstracted, result);
                var trial = new Dictionary<int, ManagedValue>(match.Binding);
                bool Agree(ManagedValue candidate, Func<ManagedValue, InlineEnd, ManagedValue> view) =>
                    Enumerable.Range(0, ends.Count).All(i => Unify(view(Instantiate(candidate, Pairs(ends[i])), ends[i]), view(held[i], ends[i]), trial));
                var function = abstracted;
                // 先按读到的值比较；不同时表示成调用后的内存：一条路径沿用读过的值，另一条路径重新读取时是同一个项。
                if (!isEdge && !mentioned)
                {
                    var current = Enumerable.Range(0, ends.Count).OrderBy(i => ends[i].Result is ConstantValue ? 1 : 0).Select(i => Current(abstracted, ends[i])).First();
                    var same = Enumerable.Range(0, ends.Count).All(i => SameTerm(held[i], held[0]));
                    if (same || !ReadsCurrent(current) || !Agree(current, Current)) continue;
                    function = current;
                }
                else if (!Agree(abstracted, (value, _) => value))
                {
                    trial = new(match.Binding);
                    function = Enumerable.Range(0, ends.Count).OrderBy(i => ends[i].Result is ConstantValue ? 1 : 0).Select(i => Current(abstracted, ends[i])).First();
                    if (!Agree(function, Current)) { match.Fail("出口复制在各路径上不同"); return null; }
                }
                foreach (var (key, value) in trial) match.Binding[key] = value;
                if (result is not null && Mentions(function, result)) used = true;
                copies.Add((target, function));
            }
            return copies;
        }
        if (predicate is null)
        {
            if (match.Ends.Any(e => e.Exit != match.Ends[0].Exit))
                return ConcludeDuplicated(match, body, blocks, result, Pairs);
            if (Copies(match.Ends) is not { } joined) return false;
            match.Exit = match.Ends[0].Exit;
            match.ExitCopies = joined;
            match.Result = used ? result : null;
            if (!used && !match.Ends.All(e => e.Result is null || NonThrowingInlineValue(e.Result)))
                return match.Fail("返回值没有承接的局部，且无法证明额外求值无副作用");
            // 只观察部分叶子时，其余叶子的求值也不能引入异常。
            if (used && !joined.Any(c => Contains(c.Value, result!)))
                foreach (var end in match.Ends)
                    foreach (var (actual, carrier) in Pairs(end).Skip(1))
                        if (!joined.Any(c => Contains(c.Value, carrier)) && !NonThrowingInlineValue(actual))
                            return match.Fail("结构体返回值未被承接的叶子无法证明额外求值无副作用");
            return true;
        }
        var sides = new Dictionary<bool, List<InlineEnd>> { [true] = [], [false] = [] };
        var covered = new HashSet<(ulong Block, int Index)>();
        bool Along(InlineEnd end, ManagedEdge edge, bool outcome)
        {
            var walker = At(end);
            var copies = end.Copies.ToList();
            foreach (var copy in edge.Copies)
            {
                if (Term(walker, copy.Value) is not { } value) return false;
                copies.Add((copy.Target, value));
            }
            if (!Follow(walker, edge)) return false;
            var trial = new InlineMatch { Binding = [], TypeArguments = match.TypeArguments };
            if (!Finish(walker, trial, null) || trial.Ends.Count != 1) return false;
            covered.UnionWith(trial.Covered);
            sides[outcome].Add(trial.Ends[0] with { Copies = copies.Concat(trial.Ends[0].Copies).ToArray(), Result = end.Result, Epoch = end.Epoch });
            return true;
        }
        foreach (var end in match.Ends)
        {
            var expected = Instantiate(predicate, Pairs(end));
            if (expected is ConstantValue constant)
            {
                if (end.Exit.Index != 0) return match.Fail("条件续接点位于块中间");
                sides[constant.Bits != 0].Add(end);
                continue;
            }
            if (At(end).Current is not ManagedBranch branch || Term(At(end), branch.Condition) is not { } condition)
                return match.Fail("返回路径不受同一条件支配");
            var canonical = Canonical(expected);
            bool same;
            if (Unify(canonical, Canonical(condition), match.Binding)) same = true;
            else if (Unify(canonical, Canonical(Negate(condition)), match.Binding)) same = false;
            else return match.Fail("返回值与调用方的比较不同");
            covered.Add(end.Exit);
            if (!Along(end, branch.Taken, same) || !Along(end, branch.Fallthrough, !same)) return false;
        }
        ManagedEdge? Edge(IReadOnlyList<InlineEnd> ends)
        {
            if (ends.Count == 0) { match.Fail("谓词只有一种结果"); return null; }
            if (ends.Any(e => e.Exit != ends[0].Exit)) { match.Fail("相同返回条件的续接点不同"); return null; }
            if (ends[0].Exit.Index != 0) { match.Fail("条件续接点位于块中间"); return null; }
            return Copies(ends) is { } copies ? new ManagedEdge(ends[0].Exit.Block, copies.Select(c => new ManagedCopy(c.Target, c.Value)).ToArray()) : null;
        }
        if (Edge(sides[true]) is not { } taken || Edge(sides[false]) is not { } fallthrough) return false;
        if (taken.Target == fallthrough.Target) return match.Fail("条件续接点相同");
        match.Covered.UnionWith(covered);
        match.Result = result;
        match.Exit = (taken.Target, 0);
        match.ExitCopies = [];
        match.Continuation = new ManagedBranch(0, predicate, taken, fallthrough);
        return true;
    }

    /// <summary>区域结束之后的读取代数：调用已经完成，这段时间内的读取看到的都是调用后的内存。</summary>
    private const int AfterRegion = 1 << 20;

    /// <summary>
    /// 路径结束时的值，表示成调用后的内存：之前读到的位置此后没有被覆盖时，它的值就是该位置现在的内容。
    /// 一条路径沿用读过的值，另一条路径在调用之后重新读取，这样两者才是同一个项。
    /// </summary>
    private static ManagedValue Current(ManagedValue value, InlineEnd end)
    {
        if (value is Observed { Epoch: var epoch, Read: var read } && epoch == end.Epoch
            && end.State is { } state && !state.Stores.Any(s => MayAlias(s.Location, read)))
            return new Observed(ManagedValues.Map(read, child => Current(child, end)), AfterRegion);
        return MapTerm(value, child => Current(child, end));
    }

    private static bool ReadsCurrent(ManagedValue value)
    {
        if (value is Observed { Epoch: AfterRegion }) return true;
        var found = false;
        MapTerm(value, child =>
        {
            found |= ReadsCurrent(child);
            return child;
        });
        return found;
    }

    /// <summary>路径上从起点开始经过的语句，止于第一个不能简单走过的语句（分支、返回等）。</summary>
    private static List<(ulong Block, int Index)> Trail(IReadOnlyDictionary<ulong, ManagedBlock> blocks, (ulong Block, int Index) start)
    {
        var trail = new List<(ulong Block, int Index)>();
        var at = start;
        while (trail.Count < 128 && !trail.Contains(at))
        {
            trail.Add(at);
            var statement = blocks[at.Block].Statements[at.Index];
            if (statement is ManagedJump jump && blocks.ContainsKey(jump.Edge.Target)) at = (jump.Edge.Target, 0);
            else if (statement is ManagedAssignment or ManagedStore or ManagedCall or ManagedCheck) at = (at.Block, at.Index + 1);
            else break;
        }
        return trail;
    }

    /// <summary>出口之后的一个可观察事件，项已经表示成调用后的内存。</summary>
    private sealed record SuffixEvent(ManagedStatement Statement, IReadOnlyList<ManagedValue> Values);

    private sealed record Suffix(InlineEnd End, Walker Walker, List<SuffixEvent> Events, List<(ulong Block, int Index)> Passed, HashSet<Variable> Assigned)
    {
        public HashSet<ManagedValue> Dereferenced { get; } = [];
    }

    /// <summary>沿路径走到 stop（null 表示走到终结语句为止），收集事件和局部的最终值。</summary>
    private Suffix? Replay(InlineEnd end, IReadOnlyDictionary<ulong, ManagedBlock> blocks, (ulong Block, int Index)? stop, IReadOnlySet<Variable> addressed)
    {
        var state = end.State!;
        var walker = new Walker
        {
            Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Epoch = AfterRegion, Calls = 1 << 16,
            Env = end.Env.ToDictionary(p => p.Key, p => Current(p.Value, end)),
            Assumptions = state.Assumptions.Select(a => (Current(a.Condition, end), a.Value)).ToList(),
            Dereferenced = state.Dereferenced.Select(d => Current(d, end)).ToHashSet(),
        };
        var suffix = new Suffix(end, walker, [], [], []);
        for (var steps = 0; steps < 256; steps++)
        {
            if ((walker.Block, walker.Index) == stop) return suffix;
            var statement = walker.Current;
            suffix.Passed.Add((walker.Block, walker.Index));
            foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk))
                if (Accessed(value) is { } receiver && Term(walker, receiver) is { } accessed && !walker.Dereferenced.Contains(accessed)) suffix.Dereferenced.Add(accessed);
            switch (statement)
            {
                case ManagedAssignment assignment:
                    if (Term(walker, assignment.Value) is not { } assigned) return null;
                    // 取过地址的局部可能经引用改变，不能只按环境比较。
                    if (addressed.Contains(assignment.Target.Variable) || ManagedValues.Walk(assignment.Value).OfType<LocalValue>().Any(l => addressed.Contains(l.Variable))) return null;
                    // 读取和计算只改变环境；分配之类的求值是事件。
                    if ((ManagedEffects.Value(assignment.Value).Kinds & ~EffectKind.Read) != 0) suffix.Events.Add(new(statement, [assigned]));
                    walker.Env[assignment.Target.Variable] = assigned;
                    suffix.Assigned.Add(assignment.Target.Variable);
                    walker.Index++;
                    break;
                case ManagedJump jump:
                    if (jump.Edge.Copies.Any(c => Term(walker, c.Value) is null) || !blocks.ContainsKey(jump.Edge.Target)) return null;
                    var values = jump.Edge.Copies.Select(c => (c.Target.Variable, Term(walker, c.Value)!)).ToArray();
                    foreach (var (variable, value) in values) { walker.Env[variable] = value; suffix.Assigned.Add(variable); }
                    walker.Block = jump.Edge.Target;
                    walker.Index = 0;
                    break;
                case ManagedStore store:
                    if (Location(walker, store.Target) is not { } location || Term(walker, store.Value) is not { } stored) return null;
                    suffix.Events.Add(new(statement, [location, stored]));
                    walker.Stores.Add((location, stored));
                    walker.Index++;
                    break;
                case ManagedCall call:
                    var arguments = ManagedValues.Of(call.Invocation).Select(a => Term(walker, a)).ToArray();
                    if (arguments.Any(a => a is null)) return null;
                    suffix.Events.Add(new(statement, arguments!));
                    if (call.Result is { } result)
                    {
                        walker.Env[result.Variable] = new Returned(walker.Calls, result.Type, result.Width);
                        suffix.Assigned.Add(result.Variable);
                    }
                    walker.Calls++;
                    walker.Epoch++;
                    walker.Stores.Clear();
                    walker.Index++;
                    break;
                case ManagedCheck check:
                    if (Term(walker, check.Condition) is not { } condition) return null;
                    suffix.Events.Add(new(statement, [condition]));
                    walker.Assumptions.Add((condition, false));
                    walker.Index++;
                    break;
                case ManagedReturn returned:
                    ManagedValue? value2 = null;
                    if (returned.Value is { } r && (value2 = Term(walker, r)) is null) return null;
                    suffix.Events.Add(new(statement, value2 is null ? [] : [value2]));
                    return suffix;
                case ManagedBranch branch:
                    if (Term(walker, branch.Condition) is not { } tested) return null;
                    suffix.Events.Add(new(statement, [tested]));
                    return suffix;
                default:
                    return null;
            }
        }
        return null;
    }

    /// <summary>
    /// 各路径出口不同：调用之后的代码被复制到了各路径。逐事件比较到它们汇合或结束，相同时只保留一份。
    /// 保留经过调用次数最多的路径：那里的编译器已知事实最少，读取都还在，代码对其他路径也成立。
    /// 其他路径只多出已知不成立的检查时等价；保留路径多出的检查和解引用，在其他路径上也要已知不会抛出。
    /// </summary>
    private bool ConcludeDuplicated(InlineMatch match, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks, LocalValue? result,
        Func<InlineEnd, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)>> pairs)
    {
        string Exits() => string.Join(", ", match.Ends.Select(e => $"0x{e.Exit.Block:x}+{e.Exit.Index}"));
        var kept = match.Ends.OrderByDescending(e => e.Epoch).First();
        var trails = match.Ends.ToDictionary(e => e, e => Trail(blocks, e.Exit));
        (ulong Block, int Index)? join = trails[kept].Select(p => ((ulong Block, int Index)?)p).FirstOrDefault(p => trails.Values.All(t => t.Contains(p!.Value)));
        var addressed = blocks.Values.SelectMany(b => b.Statements).SelectMany(ReadValues).SelectMany(ManagedValues.Walk)
            .OfType<AddressValue>().SelectMany(a => ManagedValues.Walk(a.Target)).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var suffixes = new List<Suffix>();
        foreach (var end in match.Ends)
            if (Replay(end, blocks, join, addressed) is { } replayed) suffixes.Add(replayed);
            else return match.Fail($"各路径在调用方的出口不同（后续不能比较）：{Exits()}");
        var retained = suffixes.Single(x => ReferenceEquals(x.End, kept));
        // 项里的返回值换成结果局部，才能跨路径比较。
        ManagedValue Normal(ManagedValue term, Suffix suffix) => Canonical(Fold(Abstract(term,
            pairs(suffix.End).Select(p => (Current(p.Actual, suffix.End), p.Carrier)).ToArray(), match)));
        bool Equal(ManagedValue a, Suffix x, ManagedValue b, Suffix y) => SameTerm(Normal(a, x), Normal(b, y));
        bool Passes(SuffixEvent check, Suffix on) => check.Statement is ManagedCheck && KnownCondition(check.Values[0], on.Walker, NoBinding) == false;
        foreach (var other in suffixes.Where(x => !ReferenceEquals(x, retained)))
        {
            var (i, j) = (0, 0);
            while (i < retained.Events.Count || j < other.Events.Count)
            {
                var a = i < retained.Events.Count ? retained.Events[i] : null;
                var b = j < other.Events.Count ? other.Events[j] : null;
                if (a is not null && b is not null && SameEvent(a, retained, b, other, Equal)) { i++; j++; continue; }
                if (a is not null && Passes(a, other)) { i++; continue; }
                if (b is not null && Passes(b, retained)) { j++; continue; }
                return match.Fail($"各路径在调用方的出口不同（后续不同）：{Exits()}");
            }
            // 保留的代码会在这条路径上执行：它多解引用的项在这里不能为空。
            foreach (var accessed in retained.Dereferenced)
                if (!other.Walker.Dereferenced.Contains(accessed) && !other.Dereferenced.Contains(accessed)
                    && KnownCondition(new ComparisonValue(Cond.Eq, accessed, new ConstantValue(0, accessed.Type, accessed.Width), types.Boolean), other.Walker, NoBinding) != false)
                    return match.Fail($"各路径在调用方的出口不同（后续的解引用不同）：{Exits()}");
        }
        var locals = suffixes.SelectMany(x => x.Assigned).Concat(match.Locals.Keys).Concat(match.Ends.SelectMany(e => e.Copies).Select(c => c.Target.Variable)).ToHashSet();
        var localTypes = new Dictionary<Variable, LocalValue>();
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedAssignment assignment) localTypes[assignment.Target.Variable] = assignment.Target;
            if (statement is ManagedCall { Result: { } called }) localTypes[called.Variable] = called;
            foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies)) localTypes[copy.Target.Variable] = copy.Target;
        }
        // 汇合点活跃的局部在各路径上相同。
        var verified = new HashSet<Variable>();
        if (join is { } point)
            foreach (var variable in locals)
            {
                if (!LiveAt(body, blocks, point.Block, point.Index, variable)) continue;
                var local = localTypes[variable];
                var first = retained.Walker.Env.GetValueOrDefault(variable) ?? local;
                // 一条路径重新求不变的值，另一条路径沿用区域之前保存的局部。
                bool Saved(ManagedValue a, ManagedValue b) => a is LocalValue saved && ImmutableValue(b) && SameCopyAt(body, blocks, match.Start.Block, match.Start.Index, saved.Variable, b);
                foreach (var other in suffixes)
                {
                    var second = other.Walker.Env.GetValueOrDefault(variable) ?? local;
                    if (!Equal(first, retained, second, other) && !Saved(first, second) && !Saved(second, first))
                        return match.Fail($"各路径在调用方的出口不同（汇合点的 {variable} 不同）：{Exits()}");
                }
                verified.Add(variable);
            }
        // 保留的代码在调用之后运行：它用到的、区域内定义的局部由返回值给出，或在调用之后重新读取。
        var used = false;
        var copies = new List<(LocalValue, ManagedValue)>();
        foreach (var variable in locals.Where(v => kept.Env.ContainsKey(v)))
        {
            if (!LiveAt(body, blocks, kept.Exit.Block, kept.Exit.Index, variable)) continue;
            var function = Current(Abstract(kept.Env[variable], pairs(kept), match), kept);
            var mentions = result is not null && Mentions(function, result);
            if (!mentions && !ReadsCurrent(function) && !match.Ends.SelectMany(e => e.Copies).Any(c => c.Target.Variable == variable)) continue;
            used |= mentions;
            copies.Add((localTypes[variable], function));
        }
        match.Exit = kept.Exit;
        match.ExitCopies = copies;
        match.Result = used ? result : null;
        if (!used && !match.Ends.All(e => e.Result is null || NonThrowingInlineValue(e.Result)))
            return match.Fail("返回值没有承接的局部，且无法证明额外求值无副作用");
        // 其余路径的这段代码进入区域；它们定义的局部如果在区域外使用，由区域检查拒绝。
        foreach (var other in suffixes.Where(x => !ReferenceEquals(x, retained)))
        {
            match.Covered.UnionWith(other.Passed);
            foreach (var position in other.Passed)
                if (Raises(other.Walker, blocks[position.Block].Statements[position.Index])) match.Raising.Add(position.Block);
            foreach (var variable in other.Assigned.Except(verified).Except(retained.Assigned))
            {
                match.Defined[variable] = other.Walker.Env[variable];
                match.Locals[variable] = localTypes[variable];
            }
        }
        return true;
    }

    private bool SameEvent(SuffixEvent a, Suffix x, SuffixEvent b, Suffix y, Func<ManagedValue, Suffix, ManagedValue, Suffix, bool> equal)
    {
        bool Values() => a.Values.Count == b.Values.Count && a.Values.Zip(b.Values).All(p => equal(p.First, x, p.Second, y));
        switch (a.Statement, b.Statement)
        {
            case (ManagedStore, ManagedStore): return Values();
            case (ManagedAssignment, ManagedAssignment): return Values();
            case (ManagedCall p, ManagedCall q): return p.Invocation.Method.Equals(q.Invocation.Method) && p.Invocation.Virtual == q.Invocation.Virtual && Values();
            case (ManagedCheck p, ManagedCheck q): return p.Exception.Equals(q.Exception) && Values();
            case (ManagedReturn, ManagedReturn): return Values();
            case (ManagedBranch p, ManagedBranch q):
                // 条件相同或相反，两个去向一一对应；边上的复制归入汇合后的比较时过于宽松，这里要求两边都没有复制或完全相同。
                if (!p.Taken.Copies.SequenceEqual(q.Taken.Copies) && !p.Taken.Copies.SequenceEqual(q.Fallthrough.Copies)) return false;
                if (p.Taken.Target == q.Taken.Target && p.Fallthrough.Target == q.Fallthrough.Target && p.Taken.Copies.SequenceEqual(q.Taken.Copies) && p.Fallthrough.Copies.SequenceEqual(q.Fallthrough.Copies))
                    return Values();
                if (p.Taken.Target == q.Fallthrough.Target && p.Fallthrough.Target == q.Taken.Target && p.Taken.Copies.SequenceEqual(q.Fallthrough.Copies) && p.Fallthrough.Copies.SequenceEqual(q.Taken.Copies))
                    return equal(a.Values[0], x, Negate(b.Values[0]), y);
                return false;
            default:
                return false;
        }
    }

    /// <summary>分支条件的比较形式：布尔值 b 即 b != 0，其否定即 b == 0（0/1 归一后条件可以不带显式比较）。</summary>
    private ComparisonValue? AsComparison(ManagedValue condition) => condition switch
    {
        ComparisonValue comparison => comparison,
        NegatedValue { Operand: var operand } when types.Kind(operand.Type) == TypeKind.Bool
            => new ComparisonValue(Cond.Eq, operand, new ConstantValue(0, operand.Type, operand.Width), types.Boolean),
        _ when types.Kind(condition.Type) == TypeKind.Bool
            => new ComparisonValue(Cond.Ne, condition, new ConstantValue(0, condition.Type, condition.Width), types.Boolean),
        _ => null,
    };

    private static bool? ConstantComparison(Cond condition, ConstantValue left, ConstantValue right)
    {
        if (left.Width != right.Width || left.Width is not (8 or 16 or 32 or 64)) return null;
        var a = left.Bits & Expr.Mask(left.Width);
        var b = right.Bits & Expr.Mask(right.Width);
        var sign = 1UL << (left.Width - 1);
        return condition switch
        {
            Cond.Eq => a == b, Cond.Ne => a != b,
            Cond.Ult => a < b, Cond.Ule => a <= b, Cond.Ugt => a > b, Cond.Uge => a >= b,
            Cond.Slt => (a ^ sign) < (b ^ sign), Cond.Sle => (a ^ sign) <= (b ^ sign),
            Cond.Sgt => (a ^ sign) > (b ^ sign), Cond.Sge => (a ^ sign) >= (b ^ sign),
            _ => null,
        };
    }
}
