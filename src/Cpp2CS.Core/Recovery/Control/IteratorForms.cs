using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// 迭代器的 MoveNext 还原成 Roslyn 降级后的形态，反编译器才能提升出 yield return。
/// 它要求 yield 点依次是 current = 值；state = 常量；return true。clang 按路径合并了后两步：写状态的语句移到共用的块，状态值经局部传入；
/// 返回值也经局部传入共用的 return。这里按路径复制回来，语义不变。分派和 async 一样处理。
/// 带 try 的迭代器，Roslyn 的 MoveNext 整个包在 try 里，fault 块只调用 Dispose；IL2CPP 把 fault 写成捕获后重新抛出，clang 又把 Dispose 内联进去。
/// 处理体只判断状态、运行 Dispose 或 finally 方法（可能已内联）再重新抛出时写回 fault（ECMA-335 I.12.4.2.5）：try 之外的块不会抛出，并入 try 不改变行为。
/// 内联进来的调用必须和这些方法调用的方法同名（结构体枚举器的 Dispose 恢复时已写回接口调用，方法对象不同），用户写的 catch 不满足这一点，留作内层区域。
/// 没有 finally 方法时 Roslyn 不生成 fault，区域都是用户写的。
/// try 里的状态（-3 及以下）表示正在 finally 保护的范围内。Roslyn 在进入 try 和 yield 恢复处各写一次，然后跳到循环头；clang 把这些写入合并进循环头。
/// 反编译器按状态写入划定 try 的范围，合并后恢复点跳回写状态的块，就成了离开 try 再进入，finally 会在每轮迭代运行。这里按路径拆回去，语义不变。
/// finally 方法要先写状态，读字段的语句和它可以交换。Dispose 只按状态运行 finally 方法，clang 把状态集合写成范围和位图比较，反编译器追踪不了：逐个状态求值后写回相等比较。
/// 形态不符时保持原样；反编译器放弃或提升失败时留下状态机类。
/// </summary>
public static class IteratorForms
{
    private const string CurrentName = "<>2__current";
    private const string DisposeName = "System.IDisposable.Dispose";
    private const string FinallyPrefix = "<>m__Finally";
    /// <summary>共用块最多复制多少条语句；再多就不是这几步的合并。</summary>
    private const int TailLimit = 8;

    public static ManagedBody Run(ManagedBody body, TypeRef boolean, Func<MethodRef, ManagedBody?> summary, out string? rejected)
    {
        rejected = null;
        if (body.Method.Method is not { IsStatic: false } method || body.Method.DeclaringType is not DefinitionRef { Definition: var definition } owner
            || !definition.Fields.Any(f => f.Name == StateMachineForm.StateName) || !definition.Fields.Any(f => f.Name == CurrentName)) return body;
        if (method.Name.StartsWith(FinallyPrefix, StringComparison.Ordinal)) return Form.StateFirst(body);
        if (method.Name == DisposeName) return Form.DisposeStates(body, boolean);
        if (method.Name != "MoveNext") return body;
        var form = new Form(body);
        if (body.Regions.Count > 0 && !form.Fault(owner, summary))
        {
            rejected = form.Reason ?? "try";
            return body;
        }
        var result = form.Run();
        rejected = result is null ? form.Reason ?? "unknown" : null;
        return result ?? body;
    }

    private sealed class Form(ManagedBody source) : StateMachineForm(source)
    {
        private ManagedRegion? fault;
        private ManagedStatement[] faultHandler = [];

        /// <summary>finally 方法开头读字段的语句放到写状态之后：反编译器只认第一条是写状态。入口只是一条跳转时先并掉。</summary>
        public static ManagedBody StateFirst(ManagedBody body)
        {
            var blocks = body.Blocks.ToList();
            if (blocks is [{ Statements: [ManagedJump { Edge: { Copies.Count: 0, Target: var next } }] }, ..]
                && blocks.FindIndex(b => b.Address == next) is > 0 and var index
                && !blocks.Skip(1).SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges).Any(e => e.Target == next))
            {
                blocks[0] = blocks[0] with { Statements = blocks[index].Statements };
                blocks.RemoveAt(index);
            }
            var statements = blocks[0].Statements.ToList();
            var at = statements.FindIndex(s => StateStored(s) is not null);
            if (at <= 0 || !statements.Take(at).All(s => s is ManagedAssignment { Value: FieldValue { Receiver: ArgumentValue { Index: -1 } } value } && !IsField(value, StateName))) return body;
            var store = statements[at];
            statements.RemoveAt(at);
            statements.Insert(0, store);
            blocks[0] = blocks[0] with { Statements = statements };
            return body with { Blocks = blocks };
        }

        /// <summary>状态值的枚举范围：iterator 的状态是写在 MoveNext 里的小常量。</summary>
        private const int LowestState = -64, HighestState = 256;

        /// <summary>
        /// 没有区域、每个状态最多运行一个方法的 Dispose，条件不全是和常量的相等比较时，按状态求值，写回 if (num == a || num == b) 方法()。
        /// 求值碰到状态以外的东西时保持原样。
        /// </summary>
        public static ManagedBody DisposeStates(ManagedBody body, TypeRef boolean)
        {
            if (body.Regions.Count > 0) return body;
            var blocks = body.Blocks.ToDictionary(b => b.Address);
            var first = body.Blocks[0];
            while (first.Statements is [ManagedJump { Edge: { Copies.Count: 0, Target: var target } }] && blocks.TryGetValue(target, out var following)) first = following;
            if (first.Statements.FirstOrDefault() is not ManagedAssignment { Target: var num, Value: var read } || !IsField(read, StateName)) return body;
            if (!blocks.Values.SelectMany(b => b.Statements).Any(s => s is ManagedSwitch || s is ManagedBranch { Condition: var condition } && !IsSimpleTest(condition, num.Variable))) return body;
            var calls = new Dictionary<ManagedCall, List<int>>(ReferenceEqualityComparer.Instance);
            for (var state = LowestState; state <= HighestState; state++)
            {
                var known = new Dictionary<Variable, long> { [num.Variable] = state };
                long? Leaf(ManagedValue value) => value is LocalValue local && known.TryGetValue(local.Variable, out var v) ? v : IsField(value, StateName) ? state : null;
                var at = first.Address;
                ManagedCall? ran = null;
                for (var steps = 0; ; steps++)
                {
                    if (steps > 256) return body;
                    var next = (ulong?)null;
                    foreach (var statement in blocks[at].Statements)
                    {
                        switch (statement)
                        {
                            case ManagedAssignment { Target: var assigned, Value: var value }:
                                if (ConstantConditions.Evaluate(value, Leaf) is not { } result) return body;
                                known[assigned.Variable] = result;
                                break;
                            case ManagedCall { Invocation.Method.Method.Name: var name, Result: null } call when name.StartsWith(FinallyPrefix, StringComparison.Ordinal) && ran is null:
                                ran = call;
                                break;
                            case ManagedJump { Edge: { Copies.Count: 0 } edge }:
                                next = edge.Target;
                                break;
                            case ManagedBranch { Condition: var condition, Taken: { Copies.Count: 0 } taken, Fallthrough: { Copies.Count: 0 } other }:
                                if (ConstantConditions.Evaluate(condition, Leaf) is not { } truth) return body;
                                next = truth != 0 ? taken.Target : other.Target;
                                break;
                            case ManagedSwitch { Index: var index, Cases: var cases } when cases.All(c => c.Copies.Count == 0):
                                if (ConstantConditions.Evaluate(index, Leaf) is not { } selected) return body;
                                // 越界不可达，原生代码在前驱里检查过上界；到这里说明这个状态本来就走不到，求值的前提不成立。
                                if (selected < 0 || selected >= cases.Count) return body;
                                next = cases[(int)selected].Target;
                                break;
                            case ManagedReturn { Value: null }:
                                next = null;
                                goto finished;
                            default:
                                return body;
                        }
                    }
                    if (next is null) return body;
                    at = next.Value;
                }
                finished:
                if (ran is null) continue;
                if (!calls.TryGetValue(ran, out var states)) calls[ran] = states = [];
                states.Add(state);
            }
            if (calls.Count == 0) return body;
            return Written(body, num, read, calls, boolean);
        }

        private static bool IsSimpleTest(ManagedValue condition, Variable num) =>
            condition is ComparisonValue { Condition: Cond.Eq or Cond.Ne, Left: var left, Right: ConstantValue } && IsLocal(left, num);

        private static ManagedBody Written(ManagedBody body, LocalValue num, ManagedValue read, Dictionary<ManagedCall, List<int>> calls, TypeRef boolean)
        {
            var address = body.Blocks[0].Address;
            var next = 0UL;
            ulong New() => SyntheticBase | next++ << 40;
            var end = New();
            var blocks = new List<ManagedBlock>();
            var chain = calls.ToArray();
            var tests = chain.SelectMany((c, i) => c.Value.Select(state => (Call: i, State: state))).ToArray();
            var bodies = chain.Select(_ => New()).ToArray();
            var starts = tests.Select(_ => New()).ToArray();
            blocks.Add(new ManagedBlock(address, [new ManagedAssignment(address, num, read), new ManagedJump(address, new ManagedEdge(starts[0], []))]));
            for (var i = 0; i < tests.Length; i++)
            {
                var condition = new ComparisonValue(Cond.Eq, num, new ConstantValue((uint)tests[i].State, num.Type, num.Width), boolean);
                var otherwise = i + 1 < tests.Length ? starts[i + 1] : end;
                blocks.Add(new ManagedBlock(starts[i], [new ManagedBranch(address, condition, new ManagedEdge(bodies[tests[i].Call], []), new ManagedEdge(otherwise, []))]));
            }
            for (var i = 0; i < chain.Length; i++)
                blocks.Add(new ManagedBlock(bodies[i], [chain[i].Key, new ManagedJump(address, new ManagedEdge(end, []))]));
            blocks.Add(new ManagedBlock(end, [new ManagedReturn(address, null)]));
            return body with { Blocks = blocks };
        }

        private const ulong SyntheticBase = 7UL << 60;

        /// <summary>捕获后只运行清理再重新抛出的 catch 换成 fault。异常对象不为空，判空的另一边到不了，不必比较。</summary>
        public bool Fault(DefinitionRef owner, Func<MethodRef, ManagedBody?> summary)
        {
            if (owner.Definition.Methods.FirstOrDefault(m => m.Name == DisposeName && m.Parameters.Count == 0) is not { } dispose) return Fail("try:dispose");
            var cleanups = owner.Definition.Methods.Where(m => m.Name == DisposeName || m.Name.StartsWith(FinallyPrefix, StringComparison.Ordinal)).ToHashSet();
            var inlined = cleanups.SelectMany(m => summary(new MethodRef(m, owner.Arguments, []))?.Blocks ?? []).SelectMany(b => b.Statements).OfType<ManagedCall>().Select(c => ShortName(c.Invocation.Method.Method)).ToHashSet();
            var mains = body.Regions.Where(r => r.Kind == ManagedRegionKind.Catch && r.CatchType is null && r.Exception is not null && RunsCleanup(r, cleanups, inlined)).ToArray();
            if (mains.Length == 0 && !cleanups.Any(m => m.Name.StartsWith(FinallyPrefix, StringComparison.Ordinal))) return true;
            if (mains is not [var region]) return Fail(mains.Length > 1 ? "try:several" : "try:" + (reason ?? "none"));
            var handler = region.Handler.Where(code.ContainsKey).ToHashSet();
            if (code.Where(p => !handler.Contains(p.Key)).SelectMany(p => p.Value).SelectMany(ManagedValues.Edges).Any(e => handler.Contains(e.Target))) return Fail("try:shared");
            // 原生处理块直接调用 Dispose，或是内联了它（RunsCleanup 已核对只运行清理方法的代码）；内联时执行对照按 Dispose 的方法体透明执行。
            var direct = handler.SelectMany(at => code[at]).OfType<ManagedCall>().Any(c => c.Invocation.Method.Method == dispose);
            foreach (var at in handler) code.Remove(at);
            var self = new ArgumentValue(-1, owner, 64);
            faultHandler = [
                new ManagedCall(region.HandlerEntry, new ManagedInvocation(new MethodRef(dispose, owner.Arguments, []), self, [], false), null) { Inlined = !direct },
                new ManagedEndFault(region.HandlerEntry),
            ];
            fault = region;
            return true;
        }

        private string? reason;

        private static string ShortName(MethodDef method) => method.Name[(method.Name.LastIndexOf('.') + 1)..];

        private bool RunsCleanup(ManagedRegion region, HashSet<MethodDef> cleanups, HashSet<string> inlined)
        {
            var rethrows = false;
            var runs = false;
            foreach (var statement in region.Handler.Where(code.ContainsKey).SelectMany(a => code[a]))
                switch (statement)
                {
                    case ManagedCall { Invocation.Method.Method: var target }:
                        if (!cleanups.Contains(target) && !inlined.Contains(ShortName(target)))
                        {
                            reason = "handler-call:" + target.Owner.Name + "." + target.Name;
                            return false;
                        }
                        runs = true;
                        break;
                    case ManagedStore store:
                        if (!IsThisField(store))
                        {
                            reason = "handler-store:" + store.Target.GetType().Name;
                            return false;
                        }
                        break;
                    case ManagedRethrow:
                        rethrows = true;
                        break;
                    case ManagedAssignment or ManagedBranch or ManagedJump or ManagedSwitch or ManagedReturn or ManagedThrow or ManagedCheck:
                        break;
                    default:
                        reason = "handler:" + statement.GetType().Name;
                        return false;
                }
            reason = runs && rethrows ? null : "handler-shape";
            return runs && rethrows;
        }

        public ManagedBody? Run()
        {
            num = StateLocal();
            if (num is null)
            {
                Fail("state-local");
                return null;
            }
            ThreadEmpty();
            Returns();
            StateTails();
            Returns();
            SignedRangeChecks();
            TryStateJoins();
            return HoistThis() && Yields() ? Rebuilt() : null;
        }

        /// <summary>写 try 状态的块有多个入边时，写入分到每条入边上，后面的语句留在共同的块里。</summary>
        private void TryStateJoins()
        {
            const int FirstTryState = -3;
            foreach (var join in code.Keys.ToArray())
            {
                if (join == entry || Incoming(join).Count() < 2) continue;
                // 写状态之前可能有读字段的语句，它们和写状态可以交换。
                var at = code[join].FindIndex(s => StateStored(s) is not null);
                if (at < 0 || StateStored(code[join][at]) is not <= FirstTryState) continue;
                if (!code[join].Take(at).All(s => s is ManagedAssignment { Value: FieldValue { Receiver: ArgumentValue { Index: -1 } } value } && !IsField(value, StateName))) continue;
                var store = code[join][at];
                code[join].RemoveAt(at);
                code[join].Insert(0, store);
                var rest = FreshAfter(join);
                code[rest] = code[join].Skip(1).ToList();
                code[join] = [store, new ManagedJump(store.Address, new ManagedEdge(rest, []))];
                var kept = false;
                foreach (var from in code.Keys.Where(a => a != join && a != rest).ToArray())
                    code[from] = code[from].Select(s => ManagedValues.MapEdges(s, edge =>
                    {
                        if (edge.Target != join) return edge;
                        if (!kept)
                        {
                            kept = true;
                            return edge;
                        }
                        var copy = FreshAfter(from);
                        code[copy] = [store, new ManagedJump(store.Address, new ManagedEdge(rest, []))];
                        return edge with { Target = copy };
                    })).ToList();
            }
        }

        private IEnumerable<ManagedEdge> Incoming(ulong target) => code.Values.SelectMany(s => s).SelectMany(ManagedValues.Edges).Where(e => e.Target == target);

        /// <summary>只有一条带常量复制的跳转的块：复制放到进入它的边上，共用块的入口边才有全部的值。</summary>
        private void ThreadEmpty()
        {
            for (var changed = true; changed;)
            {
                changed = false;
                foreach (var at in code.Keys.ToArray())
                    code[at] = code[at].Select(s => ManagedValues.MapEdges(s, edge =>
                    {
                        if (code[edge.Target] is not [ManagedJump { Edge: var next }] || next.Target == edge.Target || next.Copies.Count == 0 || !next.Copies.All(c => c.Value is ConstantValue)) return edge;
                        var written = next.Copies.Select(c => c.Target.Variable).ToHashSet();
                        if (edge.Copies.Any(c => written.Contains(c.Target.Variable))) return edge;
                        changed = true;
                        return new ManagedEdge(next.Target, [.. edge.Copies, .. next.Copies]);
                    })).ToList();
            }
            // 穿透之后到不了的块不能再算共用块的入口。
            var reached = Reached();
            foreach (var at in code.Keys.Where(a => !reached.Contains(a)).ToArray()) code.Remove(at);
        }

        /// <summary>return 局部，值都是边上的常量：每个值一个块。</summary>
        private void Returns()
        {
            foreach (var shared in code.Keys.ToArray())
            {
                if (code[shared] is not [ManagedReturn { Value: LocalValue result } statement]) continue;
                if (ReadElsewhere(result.Variable, statement) || !Incoming(shared).All(e => e.Copies is [{ Value: ConstantValue } only] && only.Target.Variable.Equals(result.Variable))) continue;
                var blocks = new Dictionary<ulong, ulong>();
                ManagedEdge Forward(ManagedEdge edge)
                {
                    if (edge.Target != shared) return edge;
                    var value = (ConstantValue)edge.Copies[0].Value;
                    if (!blocks.TryGetValue(value.Bits, out var block))
                    {
                        block = blocks[value.Bits] = FreshAfter(shared);
                        code[block] = [new ManagedReturn(statement.Address, value)];
                    }
                    return new ManagedEdge(block, []);
                }
                foreach (var at in code.Keys.ToArray())
                    code[at] = code[at].Select(s => ManagedValues.MapEdges(s, Forward)).ToList();
                code.Remove(shared);
            }
        }

        private static bool IsThisField(ManagedStatement statement) => statement is ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } } };

        /// <summary>写状态的共用块和它后面的块，到 return 或到别的代码为止。只有写字段的语句，写的是挂起时的状态：局部或非负常量。恢复时写 -1 的块不算。</summary>
        private List<ulong>? StateTail(ulong start)
        {
            var chain = new List<ulong>();
            var count = 0;
            var writesState = false;
            for (var at = start; ; )
            {
                var statements = code[at];
                count += statements.Count;
                if (count > TailLimit || !statements.SkipLast(1).All(IsThisField) || statements.Count == 0) return null;
                writesState |= statements.Any(s => s is ManagedStore { Value: LocalValue } store && IsField(store.Target, StateName) || StateStored(s) >= 0);
                chain.Add(at);
                if (statements[^1] is ManagedReturn) return writesState ? chain : null;
                if (statements[^1] is not ManagedJump { Edge: { Copies.Count: 0 } edge }) return null;
                // 后面是别的代码，共用块到这里为止。
                if (chain.Contains(edge.Target) || code[edge.Target].SkipLast(1).Any(s => !IsThisField(s)) || code[edge.Target][^1] is not (ManagedReturn or ManagedJump { Edge.Copies.Count: 0 })) return writesState ? chain : null;
                at = edge.Target;
            }
        }

        private void StateTails()
        {
            foreach (var shared in code.Keys.ToArray())
            {
                if (!code.ContainsKey(shared) || shared == entry || StateTail(shared) is not { } chain) continue;
                var members = chain.ToHashSet();
                var statements = chain.SelectMany(a => code[a].Where(s => s is not ManagedJump || a == chain[^1])).ToList();
                var incoming = Incoming(shared).ToArray();
                // 后面的块可以有别的入口，它们保留原样；共用块自己的入口要带上全部的值。
                var read = statements.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
                var passed = incoming.SelectMany(e => e.Copies).Select(c => c.Target.Variable).ToHashSet();
                bool Provides(ManagedEdge edge) => edge.Copies.All(c => c.Value is ConstantValue or LocalValue) && read.Where(passed.Contains).All(v => edge.Copies.Any(c => c.Target.Variable.Equals(v)));
                // 传入的局部除了这里没有别的读者，否则复制不能丢。
                bool ReadOutside(Variable variable) => code.Where(p => !members.Contains(p.Key)).SelectMany(p => p.Value)
                    .SelectMany(s => (s is ManagedAssignment assignment ? [assignment.Value] : ManagedValues.Of(s))).SelectMany(ManagedValues.Walk).Any(v => IsLocal(v, variable));
                if (!incoming.All(Provides) || passed.Any(ReadOutside) || passed.Any(v => !read.Contains(v))) continue;
                List<ManagedStatement> Copy(ManagedEdge edge)
                {
                    var values = edge.Copies.ToDictionary(c => c.Target.Variable, c => c.Value);
                    ManagedValue Replace(ManagedValue value) => value is LocalValue local && values.TryGetValue(local.Variable, out var known) ? known : ManagedValues.Map(value, Replace);
                    return statements.Select(s => ManagedValues.Map(s, Replace)).ToList();
                }
                foreach (var at in code.Keys.Where(a => a != shared).ToArray())
                {
                    var list = code[at];
                    for (var i = list.Count - 1; i >= 0; i--)
                    {
                        if (list[i] is ManagedJump { Edge: var edge } && edge.Target == shared)
                        {
                            list.RemoveAt(i);
                            list.InsertRange(i, Copy(edge));
                            continue;
                        }
                        list[i] = ManagedValues.MapEdges(list[i], e =>
                        {
                            if (e.Target != shared) return e;
                            var block = FreshAfter(at);
                            code[block] = Copy(e);
                            return new ManagedEdge(block, []);
                        });
                    }
                }
                code.Remove(shared);
            }
        }

        private static bool IsCurrentStore(ManagedStatement statement) => statement is ManagedStore store && IsField(store.Target, CurrentName);
        private static bool IsConstantStateStore(ManagedStatement statement) => StateStored(statement) is not null;
        private bool ReturnsTrue(ulong at, int index)
        {
            for (var steps = 0; steps < Budget; steps++)
                switch (code[at].ElementAtOrDefault(index))
                {
                    case ManagedJump { Edge: { Copies.Count: 0 } edge }: (at, index) = (edge.Target, 0); break;
                    case ManagedReturn { Value: ConstantValue { Bits: 1 } }: return true;
                    default: return false;
                }
            return false;
        }

        /// <summary>
        /// 每个 yield 点依次写 current、写常量状态、return true。clang 可能调换这几个写字段的语句，值已经算好时调整回来：
        /// 写 current 在写状态之后，或者中间夹着写别的字段（不会抛出）。连续两次写状态时前一次没有读者。
        /// </summary>
        private bool Yields()
        {
            var reached = Reached();
            foreach (var at in reached)
            {
                var list = code[at];
                if (list.Any(s => s is ManagedStore store && IsField(store.Target, StateName) && StateStored(s) is null)) return Fail("state:not-constant");
                for (var i = 0; i < list.Count; i++)
                {
                    if (list[i] is not ManagedStore { Value: var value } || !IsCurrentStore(list[i])) continue;
                    var ready = value is LocalValue or ConstantValue;
                    if (i > 0 && ready && IsConstantStateStore(list[i - 1]))
                    {
                        (list[i - 1], list[i]) = (list[i], list[i - 1]);
                        i--;
                    }
                    var next = i + 1;
                    while (ready && next < list.Count && IsOtherField(list[next])) next++;
                    if (next > i + 1)
                    {
                        var store = list[i];
                        list.RemoveAt(i);
                        list.Insert(next - 1, store);
                        i = next - 1;
                    }
                    while (i + 2 < list.Count && IsConstantStateStore(list[i + 1]) && IsConstantStateStore(list[i + 2])) list.RemoveAt(i + 1);
                    if (i + 1 >= list.Count || !IsConstantStateStore(list[i + 1])) return Fail($"yield:after:{list.ElementAtOrDefault(i + 1)?.GetType().Name}");
                    if (!ReturnsTrue(at, i + 2)) return Fail("yield:return");
                }
            }
            return true;
        }

        private static bool IsOtherField(ManagedStatement statement) => statement is ManagedStore store && IsThisField(store)
            && !IsField(store.Target, StateName) && !IsField(store.Target, CurrentName) && ManagedValues.Walk(store.Value).All(v => v is LocalValue or ConstantValue or BinaryValue or ConversionValue or ComparisonValue or NegatedValue);

        private HashSet<ulong> Reached()
        {
            var reached = new HashSet<ulong>();
            var work = new Stack<ulong>();
            work.Push(entry);
            // 内层区域的处理块没有边连到，要从区域本身算起。
            foreach (var inner in body.Regions.Where(r => !ReferenceEquals(r, fault))) work.Push(inner.HandlerEntry);
            while (work.TryPop(out var at))
                if (reached.Add(at))
                    foreach (var edge in code[at].SelectMany(ManagedValues.Edges)) work.Push(edge.Target);
            return reached;
        }

        private ManagedBody Rebuilt()
        {
            var reached = Reached();
            var followers = added.ToLookup(a => a.Origin, a => a.Block);
            IEnumerable<ulong> Placed(ulong block) => followers[block].SelectMany(Placed).Prepend(block);
            var layout = body.Blocks.Select(b => b.Address).SelectMany(Placed).Where(reached.Contains).ToArray();
            var blocks = layout.Select(a => new ManagedBlock(a, code[a]));
            var inner = body.Regions.Where(r => !ReferenceEquals(r, fault))
                .Select(r => r with { Try = r.Try.SelectMany(Placed).Where(reached.Contains).ToArray(), Handler = r.Handler.SelectMany(Placed).Where(reached.Contains).ToArray() }).ToArray();
            if (fault is not { } region) return body with { Blocks = blocks.ToArray(), Regions = inner };
            var handler = Fresh();
            return body with
            {
                Blocks = [.. blocks, new ManagedBlock(handler, faultHandler)],
                Regions = [.. inner, region with { Try = layout, HandlerEntry = handler, Handler = [handler], Exception = null, Kind = ManagedRegionKind.Fault }],
            };
        }
    }
}
