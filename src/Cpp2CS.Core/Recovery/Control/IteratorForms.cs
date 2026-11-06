using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// 迭代器的 MoveNext 还原成 Roslyn 降级后的形态，反编译器才能提升出 yield return。
/// 它要求 yield 点依次是 current = 值；state = 常量；return true。clang 按路径合并了后两步：写状态的语句移到共用的块，状态值经局部传入；
/// 返回值也经局部传入共用的 return。这里按路径复制回来，语义不变。分派和 async 一样处理。
/// 带 try 的迭代器还要还原 finally 方法和 fault 块，这里不处理。形态不符时保持原样，反编译器也会放弃提升，不会输出错误的代码。
/// </summary>
public static class IteratorForms
{
    private const string CurrentName = "<>2__current";
    /// <summary>共用块最多复制多少条语句；再多就不是这几步的合并。</summary>
    private const int TailLimit = 8;

    public static ManagedBody Run(ManagedBody body, out string? rejected)
    {
        rejected = null;
        if (body.Method.Method is not { Name: "MoveNext", IsStatic: false } || body.Method.DeclaringType is not DefinitionRef { Definition: var definition }
            || !definition.Fields.Any(f => f.Name == StateMachineForm.StateName) || !definition.Fields.Any(f => f.Name == CurrentName)) return body;
        if (body.Regions.Count > 0)
        {
            rejected = "try";
            return body;
        }
        var form = new Form(body);
        var result = form.Run();
        rejected = result is null ? form.Reason ?? "unknown" : null;
        return result ?? body;
    }

    private sealed class Form(ManagedBody source) : StateMachineForm(source)
    {
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
            return HoistThis() && Yields() ? Rebuilt() : null;
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
            return body with { Blocks = body.Blocks.Select(b => b.Address).SelectMany(Placed).Where(reached.Contains).Select(a => new ManagedBlock(a, code[a])).ToArray() };
        }
    }
}
