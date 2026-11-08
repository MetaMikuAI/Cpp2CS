using Cpp2CS.Ir;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 内联区域的出口。模板每条返回路径在调用方的终点由 <see cref="Finish"/> 求出：先纳入组成返回值的分段读取，再沿无条件跳转到达续接点。
/// 调用方在续接点观察到的值都是返回值的函数：对一条路径上的值把返回值抽象成结果局部，得到函数 f，再逐路径代入验证。
/// 布尔承接、零扩展、字段投影和比较都只是 f 的不同形式；条件续接的谓词同样如此，常量返回路径直接按谓词的取值选择续接。
/// 各路径的出口不同时，比较它们之后的代码：clang 常把调用之后的代码复制到各路径，等价就是同一个续接（<see cref="ConcludeDuplicated"/>）。
/// </summary>
internal sealed partial class TemplateRecovery
{
    private bool ConcludeExit(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        if (ConcludeReturn(match, method)) return true;
        var binding = new Dictionary<int, ManagedValue>(match.Binding);
        // 不读内存的返回值用在好几个语句里：续接只把第一处接到结果上，其他用处还会引用区域内的局部。
        var manyUses = match.Ends is [{ Exit: var exit }, ..] && match.Ends.All(e => e.State is not null && e.Exit == exit
                && e.Result is { } result && !ReadsMemory(result) && result is not (ConstantValue or LocalValue or ArgumentValue))
            && RewritePureUses(match.Ends, NewLocal(method.Concrete(method.Method.ReturnType)), match, blocks).Count > 1;
        RestoreBinding(match, binding);
        if (manyUses && ConcludeAtUses(match, method, body, blocks)) return true;
        RestoreBinding(match, binding);
        if (ConcludeContinuation(match, method, body, blocks)) return true;
        RestoreBinding(match, binding);
        return ConcludeAtUses(match, method, body, blocks);
    }

    /// <summary>失败的尝试不留下绑定。</summary>
    private static void RestoreBinding(InlineMatch match, IReadOnlyDictionary<int, ManagedValue> binding)
    {
        match.Binding.Clear();
        foreach (var (key, value) in binding) match.Binding[key] = value;
    }

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
            continuation |= caller.Index == 0 && Predecessors(caller.Blocks, caller.Block).Length > 1;
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
        continuation |= caller.Index == 0 && Predecessors(caller.Blocks, caller.Block).Length > 1;
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
                if (Predecessors(caller.Blocks, jump.Edge.Target).Length > 1)
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
            if (binding is null)
            {
                if (!SkipUnrelatedReads(caller, match, result, terms)) return true;
                continue;
            }
            foreach (var (key, bound) in binding) match.Binding[key] = bound;
            Cover(caller, match);
            NoteEarlyReads(value, caller, match);
            caller.Env[assignment.Target.Variable] = value;
            match.Defined[assignment.Target.Variable] = value;
            match.Locals[assignment.Target.Variable] = assignment.Target;
            caller.Index++;
            if (complete) return true;
        }
        return false;
    }

    /// <summary>
    /// 返回项的读取之间夹着无关的读取（clang 重排了相邻的读取）：后面确实还有返回项时，无关读取移出区域。
    /// 读取没有效果，和模板的读取交换不改变读到的值，接收者为空时都是空引用异常；这期间路径上不能已有写入。
    /// </summary>
    private bool SkipUnrelatedReads(Walker caller, InlineMatch match, ManagedValue result, IReadOnlyList<ManagedValue> terms)
    {
        if (caller.Stores.Count > 0) return false;
        var probe = caller.Clone();
        var passed = new List<ManagedValue?>();
        for (var steps = 0; steps < 32; steps++)
        {
            if (probe.Index >= probe.Blocks[probe.Block].Statements.Count) return false;
            if (probe.Current is ManagedJump jump)
            {
                if (jump.Edge.Copies.Count > 0 || Predecessors(probe.Blocks, jump.Edge.Target).Length > 1 || !Follow(probe, jump.Edge)) return false;
                passed.Add(null);
                continue;
            }
            if (probe.Current is not ManagedAssignment { ExceptionArrival: false } assignment || Term(probe, assignment.Value) is not { } value) return false;
            if (new[] { result }.Concat(terms).Any(expected => Unify(expected, value, new(match.Binding)))) break;
            if ((ManagedEffects.Value(assignment.Value).Kinds & ~EffectKind.Read) != 0) return false;
            probe.Env[assignment.Target.Variable] = value;
            probe.Index++;
            passed.Add(value);
        }
        if (passed.Count == 0 || passed.Count >= 32) return false;
        foreach (var value in passed)
        {
            Cover(caller, match);
            if (value is null)
            {
                if (!Follow(caller, ((ManagedJump)caller.Current).Edge)) return false;
                continue;
            }
            var assignment = (ManagedAssignment)caller.Current;
            match.Interleaved.Add((caller.Block, caller.Index, match.Effects));
            caller.Env[assignment.Target.Variable] = value;
            caller.Index++;
        }
        return true;
    }

    /// <summary>
    /// 返回值没有落到局部里，而是整个作为子表达式用在区域之后（取值方法内联后结果直接参与计算）。各路径出口相同时，从出口沿直线往后
    /// 找在每条路径上项都等于该路径返回值的子表达式，换成结果局部后再比对出口；读取按路径上的写入和调用分代，项相同就是同一个值。
    /// 调用写在区域开头，所以返回值读取的接收者在各路径上必须已经解引用过或已知非空，否则空引用异常会提前。
    /// </summary>
    private bool ConcludeAtUses(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        var ends = match.Ends;
        if (ends.Count == 0 || ends.Any(e => e.Result is null || e.State is null || e.Exit != ends[0].Exit)) return false;
        var memory = ends.Any(e => ReadsMemory(e.Result!));
        var returnType = method.Concrete(method.Method.ReturnType);
        if (ends.Any(e => e.Result is not ConstantValue && !e.Result!.Type.Equals(returnType))) return false;
        // 出口块还有区域外的入口时，它的语句不只属于这个区域。
        var exit = ends[0].Exit;
        if (exit.Index == 0 && Predecessors(blocks, exit.Block).Any(p => !match.Covered.Contains((p.Address, p.Statements.Count - 1)))) return false;
        var result = NewLocal(returnType);
        var failure = match.Failure;
        var binding = new Dictionary<int, ManagedValue>(match.Binding);
        var rewritten = memory ? RewriteUses(ends, result, match, blocks) : RewritePureUses(ends, result, match, blocks);
        if (rewritten.Count > 0)
        {
            var (rewrittenBody, rewrittenBlocks) = Rewritten(body, blocks, rewritten);
            match.Failure = null;
            match.Rewritten = rewritten;
            match.ResultAtUses = result;
            if (ConcludeContinuation(match, method, rewrittenBody, rewrittenBlocks) && ends.All(end => ReadReceivers(Bind(end.Result!, match.Binding)).All(receiver => end.State!.Dereferenced.Contains(receiver)
                || KnownCondition(new ComparisonValue(Cond.Eq, receiver, new ConstantValue(0, receiver.Type, receiver.Width), types.Boolean), end.State, NoBinding) == false)))
                return true;
        }
        RestoreBinding(match, binding);
        match.Rewritten = null;
        match.ResultAtUses = null;
        match.Failure = failure;
        return false;
    }

    private static bool ReadsMemory(ManagedValue term)
    {
        if (term is Observed) return true;
        var found = false;
        MapTerm(term, child =>
        {
            found |= ReadsMemory(child);
            return child;
        });
        return found;
    }

    /// <summary>
    /// 返回值不读内存时只取决于区域内定义的局部：这些局部在区域之外没有再赋值的话，出口之后任何位置上相同的子表达式都等于返回值，
    /// 不用按路径分代。一个返回值参与多个分支比较（switch）时用处分布在好几个块里。
    /// </summary>
    private Dictionary<(ulong Block, int Index), ManagedStatement> RewritePureUses(IReadOnlyList<InlineEnd> ends, LocalValue result, InlineMatch match, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        var rewritten = new Dictionary<(ulong Block, int Index), ManagedStatement>();
        bool Outside((ulong Block, int Index) at) => !match.Covered.Contains(at);
        foreach (var block in blocks.Values)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                var assigned = (statement is ManagedAssignment assignment ? new[] { assignment.Target.Variable } : [])
                    .Concat(statement is ManagedCall { Result: { } called } ? [called.Variable] : [])
                    .Concat(ManagedValues.Edges(statement).SelectMany(e => e.Copies).Select(c => c.Target.Variable));
                if (Outside((block.Address, i)) && assigned.Any(match.Defined.ContainsKey)) return rewritten;
            }
        var walkers = ends.Select(end => (End: end, Walker: new Walker { Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Env = new(end.Env) })).ToArray();
        var hit = false;
        ManagedValue Rewrite(ManagedValue value)
        {
            if (value is LocalValue or ArgumentValue or ConstantValue) return value;
            var trial = new Dictionary<int, ManagedValue>(match.Binding);
            if (walkers.All(w => Term(w.Walker, value) is { } term && !ReadsMemory(term) && Same(w.End.Result!, term, w.Walker, trial)))
            {
                foreach (var (key, bound) in trial) match.Binding[key] = bound;
                hit = true;
                return result;
            }
            return ManagedValues.Map(value, Rewrite);
        }
        var seen = new HashSet<ulong>();
        var pending = new Stack<(ulong Block, int Index)>([ends[0].Exit]);
        while (pending.TryPop(out var at))
        {
            if (!seen.Add(at.Block)) continue;
            var statements = blocks[at.Block].Statements;
            for (var i = at.Index; i < statements.Count; i++)
            {
                hit = false;
                var mapped = ManagedValues.Map(statements[i], Rewrite, target => target);
                if (hit && Outside((at.Block, i))) rewritten[(at.Block, i)] = mapped;
                foreach (var edge in ManagedValues.Edges(statements[i])) pending.Push((edge.Target, 0));
            }
        }
        return rewritten;
    }

    /// <summary>从共同的出口沿直线往后，把每条路径上项都等于返回值的子表达式换成结果局部；进入有其他前驱的块或遇到分支之后，局部的值不再由这些路径决定。</summary>
    private Dictionary<(ulong Block, int Index), ManagedStatement> RewriteUses(IReadOnlyList<InlineEnd> ends, LocalValue result, InlineMatch match, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        var rewritten = new Dictionary<(ulong Block, int Index), ManagedStatement>();
        var walkers = ends.Select(end => (End: end, Walker: new Walker
        {
            Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Env = new(end.Env), Epoch = end.Epoch,
            Stores = [.. end.State!.Stores], Assumptions = [.. end.State.Assumptions], Calls = 1 << 16,
        })).ToArray();
        var hit = false;
        ManagedValue Rewrite(ManagedValue value)
        {
            if (value is LocalValue or ArgumentValue or ConstantValue) return value;
            var trial = new Dictionary<int, ManagedValue>(match.Binding);
            if (walkers.All(w => Term(w.Walker, value) is { } term && Same(w.End.Result!, term, w.Walker, trial)))
            {
                foreach (var (key, bound) in trial) match.Binding[key] = bound;
                hit = true;
                return result;
            }
            return ManagedValues.Map(value, Rewrite);
        }
        var (block, index) = ends[0].Exit;
        for (var steps = 0; steps < 64 && index < blocks[block].Statements.Count; steps++)
        {
            var statement = blocks[block].Statements[index];
            hit = false;
            var mapped = ManagedValues.Map(statement, Rewrite, target => target);
            if (hit) rewritten[(block, index)] = mapped;
            foreach (var (_, walker) in walkers)
                switch (statement)
                {
                    case ManagedAssignment assignment:
                        if (Term(walker, assignment.Value) is not { } value) return rewritten;
                        walker.Env[assignment.Target.Variable] = value;
                        break;
                    case ManagedStore store:
                        if (Location(walker, store.Target) is not { } location || Term(walker, store.Value) is not { } stored) return rewritten;
                        walker.Stores.Add((location, stored));
                        break;
                    case ManagedCheck:
                        break;
                    case ManagedCall call:
                        if (call.Result is { } kept) walker.Env[kept.Variable] = new Returned(walker.Calls, kept.Type, kept.Width);
                        walker.Calls++;
                        walker.Epoch++;
                        walker.Stores.Clear();
                        break;
                    case ManagedJump jump:
                        if (Predecessors(blocks, jump.Edge.Target).Length > 1 || !Follow(walker, jump.Edge)) return rewritten;
                        break;
                    default:
                        return rewritten;
                }
            if (statement is ManagedJump next) (block, index) = (next.Edge.Target, 0);
            else index++;
            foreach (var (_, walker) in walkers) (walker.Block, walker.Index) = (block, index);
        }
        return rewritten;
    }

    /// <summary>应用用处替换后的方法体。</summary>
    private static (ManagedBody Body, IReadOnlyDictionary<ulong, ManagedBlock> Blocks) Rewritten(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks,
        IReadOnlyDictionary<(ulong Block, int Index), ManagedStatement> rewritten)
    {
        var result = blocks.ToDictionary(p => p.Key, p => p.Value);
        foreach (var group in rewritten.GroupBy(r => r.Key.Block))
        {
            var statements = result[group.Key].Statements.ToArray();
            foreach (var (position, statement) in group) statements[position.Index] = statement;
            result[group.Key] = result[group.Key] with { Statements = statements };
        }
        return (body with { Blocks = body.Blocks.Select(b => result[b.Address]).ToArray() }, result);
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
                var fieldType = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
                var access = new FieldValue(carrier, field, fieldType, Width(fieldType));
                if (fields.Accessible(field, carrier.Type)) carrier = access;
                else if (Accessor(field, fieldType, false, carrier.Type) is { } getter) carrier = access with { Accessor = getter };
                else { accessible = false; break; }
            }
            if (accessible && ManagedProjections.Project(types, Composed(returned), projection, field => new Observed(field, end.Epoch)) is { Value: var value })
                yield return (value, carrier);
        }
    }

    /// <summary>透明构造的结构体就是构造函数写入的各个字段；写入值须是常量或形参，否则保持原样。</summary>
    private ManagedValue Composed(ManagedValue value)
    {
        if (value is not NewObjectValue { Transparent: true, Constructor: { DeclaringType: DefinitionRef structure } constructor } construction
            || ConstructorWrites(constructor) is not { } writes
            || writes.Any(w => w.Value is not (ConstantValue or ArgumentValue { Index: >= 0 }))) return value;
        var arguments = Enumerable.Range(0, construction.Arguments.Count).ToDictionary(i => i, i => construction.Arguments[i]);
        return new ComposedValue(structure, writes.Select(w => (w.Path, Bind(w.Value, arguments))).ToArray());
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
            // 返回窄字段的扩展（int Y => _y）：调用方保留的窄值是结果的截断。
            if (actual is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: var narrow } && Unify(narrow, value, new(match.Binding)))
                return new ConversionValue(ConvKind.Truncate, carrier, value.Type, value.Width);
        }
        return MapTerm(value, child => Abstract(child, carriers, match));
    }

    /// <summary>
    /// 出口复制的候选与这条路径保存的值都是调用方的项，只有代入的返回值是模板的项：返回值中的形参写成 <see cref="FormalValue"/>，
    /// 合一时只绑定它们，调用方自己的实参按原样比较。
    /// </summary>
    private bool AgreeAt(ManagedValue candidate, Func<ManagedValue, InlineEnd, ManagedValue> view, InlineEnd end,
        IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> pairs, ManagedValue held, Dictionary<int, ManagedValue> binding)
    {
        var trial = new Dictionary<int, ManagedValue>(binding);
        if (!Unify(view(Instantiate(candidate, Formal(pairs)), end), view(held, end), trial, bindArguments: false)) return false;
        foreach (var (key, value) in trial) binding[key] = value;
        return true;
    }

    private static bool MentionsArgument(ManagedValue value)
    {
        if (value is ArgumentValue) return true;
        var found = false;
        MapTerm(value, child => { found |= MentionsArgument(child); return child; });
        return found;
    }

    private static (ManagedValue Actual, ManagedValue Carrier)[] Formal(IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> pairs) =>
        pairs.Select(p => (Formal(p.Actual), p.Carrier)).ToArray();

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
            ConversionValue { Kind: ConvKind.Truncate, Width: var width, Operand: ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: var narrow } } when narrow.Width == width => narrow,
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
        var result = isVoid ? null : match.ResultAtUses ?? NewLocal(returnType);
        IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> Pairs(InlineEnd end) => result is null ? [] : Carriers(end, returnType, result).ToArray();
        Walker At(InlineEnd end) => new() { Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Env = new(end.Env), Epoch = end.Epoch };
        // 谓词取自一条在续接点按返回值分支的路径。
        ManagedValue? predicate = null;
        // 不读内存的返回值已经换成结果局部时，分支原地留在调用之后，不需要按返回值分析。
        if (result is not null && !(match.ResultAtUses is not null && !match.Ends.Any(e => ReadsMemory(e.Result!))))
            foreach (var end in match.Ends.OrderBy(e => e.Result is ConstantValue ? 1 : 0))
            {
                if (At(end).Current is not ManagedBranch branch || Term(At(end), branch.Condition) is not { } tested) continue;
                var abstracted = Abstract(tested, Pairs(end), match);
                if (Mentions(abstracted, result)) { predicate = abstracted; break; }
            }
        var used = match.ResultAtUses is not null;
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
                    Enumerable.Range(0, ends.Count).All(i => AgreeAt(candidate, view, ends[i], Pairs(ends[i]), held[i], trial));
                var function = abstracted;
                // 先按读到的值比较；不同时表示成调用后的内存：一条路径沿用读过的值，另一条路径重新读取时是同一个项。
                if (!isEdge && !mentioned)
                {
                    var current = Enumerable.Range(0, ends.Count).OrderBy(i => ends[i].Result is ConstantValue ? 1 : 0).Select(i => Current(abstracted, ends[i])).First();
                    var same = Enumerable.Range(0, ends.Count).All(i => SameTerm(held[i], held[0]));
                    if (same || !ReadsCurrent(current) || !Agree(current, Current)) continue;
                    function = current;
                    match.Forms.Add("current");
                }
                else if (!Agree(abstracted, (value, _) => value))
                {
                    trial = new(match.Binding);
                    function = Enumerable.Range(0, ends.Count).OrderBy(i => ends[i].Result is ConstantValue ? 1 : 0).Select(i => Current(abstracted, ends[i])).First();
                    if (!Agree(function, Current)) { match.Fail("出口复制在各路径上不同"); return null; }
                    match.Forms.Add("current");
                }
                foreach (var (key, value) in trial) match.Binding[key] = value;
                if (MentionsArgument(function)) match.Forms.Add("caller-argument");
                if (result is not null && Mentions(function, result)) used = true;
                copies.Add((target, function));
            }
            return copies;
        }
        var separate = match.Ends.Any(e => e.Exit != match.Ends[0].Exit);
        if (predicate is null)
        {
            if (separate) return ConcludeDuplicated(match, body, blocks, result, Pairs);
            if (Copies(match.Ends) is not { } joined) return false;
            match.Exit = match.Ends[0].Exit;
            match.ExitCopies = joined;
            match.Result = used ? result : null;
            if (!used && !match.Ends.All(e => e.Result is null || NonThrowingInlineValue(e.Result)))
                return match.Fail("返回值没有承接的局部，且无法证明额外求值无副作用");
            // 只观察部分叶子时，其余叶子的求值也不能引入异常。
            if (used && match.ResultAtUses is null && !joined.Any(c => Contains(c.Value, result!)))
                foreach (var end in match.Ends)
                    foreach (var (actual, carrier) in Pairs(end).Skip(1))
                        if (!joined.Any(c => Contains(c.Value, carrier)) && !NonThrowingInlineValue(actual))
                            return match.Fail("结构体返回值未被承接的叶子无法证明额外求值无副作用");
            return true;
        }
        // 谓词的同一结果落在不同续接点时，比较这些续接；为此先保留绑定，失败的尝试不留下痕迹。
        var binding = new Dictionary<int, ManagedValue>(match.Binding);
        if (ConcludeBranch()) return true;
        if (!separate) return false;
        RestoreBinding(match, binding);
        match.Failure = null;
        return ConcludeDuplicated(match, body, blocks, result, Pairs);

        bool ConcludeBranch()
        {
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
            // 谓词是调用方的项，代入的返回值是模板的项（见 AgreeAt）。
            var expected = Instantiate(predicate, Formal(Pairs(end)));
            if (MentionsArgument(predicate)) match.Forms.Add("caller-argument");
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
            if (Unify(canonical, Canonical(condition), match.Binding, bindArguments: false)) same = true;
            else if (Unify(canonical, Canonical(Negate(condition)), match.Binding, bindArguments: false)) same = false;
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
    }

    /// <summary>区域结束之后的读取代数：调用已经完成，这段时间内的读取看到的都是调用后的内存。</summary>
    private const int AfterRegion = 1 << 20;

    /// <summary>
    /// 路径结束时的值，表示成调用后的内存：之前读到的位置此后没有被覆盖时，它的值就是该位置现在的内容。
    /// 一条路径沿用读过的值，另一条路径在调用之后重新读取，这样两者才是同一个项。
    /// 区域对这个位置只有一次写入、写的是这次读到的值加常量（如 _version++）时，读到的值等于现在的内容减去这个常量：
    /// clang 把后一次内联的自增提进前一次的各条路径时，一条路径按已知值写 v+2，另一条路径在调用之后重读再加 1。
    /// </summary>
    private static ManagedValue Current(ManagedValue value, InlineEnd end)
    {
        if (value is Observed { Epoch: var epoch, Read: var read } && epoch == end.Epoch && end.State is { } state)
        {
            var aliasing = state.Stores.Where(s => MayAlias(s.Location, read)).ToArray();
            var now = new Observed(ManagedValues.Map(read, child => Current(child, end)), AfterRegion);
            if (aliasing.Length == 0) return now;
            if (aliasing is [(var location, BinaryValue { Op: BinOp.Add, Left: Observed incremented, Right: ConstantValue step })]
                && incremented.Equals(value) && Unobserve(location).Equals(Unobserve(read)) && read.Width is 8 or 16 or 32 or 64)
                return new BinaryValue(BinOp.Add, now, step with { Bits = (0 - step.Bits) & Expr.Mask(read.Width) }, read.Type, read.Width);
        }
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
