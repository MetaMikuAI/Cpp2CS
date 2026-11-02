using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>
/// 退出 SSA 时的复制合并。φ 在每条入边上由并行复制赋值；复制两端类型相同且不冲突时合成同一个局部，复制成为恒等后删去。
/// 冲突按活跃性判定：一个局部在另一个的定义点之后仍活跃即冲突。复制 t := s 本身不使两者冲突，
/// 但在并行复制中 s 同时也是被写的目标时，复制之后 s 已不是原值，仍算冲突。
/// 异常可能在 try 块的任一处发生，处理入口活跃的局部在整个 try 块内活跃。
/// 取过地址的局部、在入口处活跃的局部（读取依赖 IL 的零初始化）不参与合并。
/// </summary>
internal static class LocalCoalescing
{
    public static ManagedBody Run(ManagedBody body)
    {
        var blocks = body.Blocks;
        if (blocks.Count == 0 || blocks.Any(b => b.Statements.SkipLast(1).Any(s => ManagedValues.Edges(s).Count > 0))) return body;
        var index = new Dictionary<ulong, int>();
        for (var i = 0; i < blocks.Count; i++) index[blocks[i].Address] = i;
        var info = new Dictionary<Variable, LocalValue>();
        var addressed = new HashSet<Variable>();
        void Note(ManagedValue value)
        {
            foreach (var item in ManagedValues.Walk(value))
            {
                if (item is LocalValue local) info.TryAdd(local.Variable, local);
                if (item is AddressValue { Target: LocalValue target }) addressed.Add(target.Variable);
            }
        }
        foreach (var statement in blocks.SelectMany(b => b.Statements))
        {
            foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement))) Note(value);
            foreach (var target in Definitions(statement).Concat(ManagedValues.Edges(statement).SelectMany(e => e.Copies).Select(c => c.Target)))
                info.TryAdd(target.Variable, target);
        }
        foreach (var region in body.Regions)
            if (region.Exception is { } exception) info.TryAdd(exception.Variable, exception);

        // 处理块：try 块内处处活跃的处理入口；catch 入口定义异常局部。
        var handlers = new List<int>[blocks.Count];
        for (var i = 0; i < blocks.Count; i++) handlers[i] = [];
        var caught = new Dictionary<int, Variable>();
        foreach (var region in body.Regions)
        {
            if (!index.TryGetValue(region.HandlerEntry, out var entry)) return body;
            foreach (var address in region.Try)
                if (index.TryGetValue(address, out var at)) handlers[at].Add(entry);
            if (region.Exception is { } exception) caught[entry] = exception.Variable;
        }

        var liveIn = new HashSet<Variable>[blocks.Count];
        for (var i = 0; i < blocks.Count; i++) liveIn[i] = [];
        HashSet<Variable>? Out(int block)
        {
            var live = new HashSet<Variable>();
            foreach (var edge in ManagedValues.Edges(blocks[block].Statements[^1]))
            {
                if (!index.TryGetValue(edge.Target, out var target)) return null;
                var written = edge.Copies.Select(c => c.Target.Variable).ToHashSet();
                live.UnionWith(liveIn[target].Where(v => !written.Contains(v)));
                foreach (var copy in edge.Copies) live.UnionWith(Uses(copy.Value));
            }
            foreach (var handler in handlers[block]) live.UnionWith(liveIn[handler]);
            return live;
        }
        HashSet<Variable> Handling(int block) => handlers[block].SelectMany(h => liveIn[h]).ToHashSet();

        for (var changed = true; changed;)
        {
            changed = false;
            for (var i = blocks.Count - 1; i >= 0; i--)
            {
                if (Out(i) is not { } live) return body;
                var handling = Handling(i);
                foreach (var statement in blocks[i].Statements.Reverse())
                {
                    foreach (var defined in Definitions(statement)) live.Remove(defined.Variable);
                    live.UnionWith(StatementUses(statement));
                    live.UnionWith(handling);
                }
                if (caught.TryGetValue(i, out var exception)) live.Remove(exception);
                if (!live.SetEquals(liveIn[i])) { liveIn[i] = live; changed = true; }
            }
        }

        var neighbors = new Dictionary<Variable, HashSet<Variable>>();
        void Interfere(Variable a, Variable b)
        {
            if (a.Equals(b)) return;
            (neighbors.TryGetValue(a, out var x) ? x : neighbors[a] = []).Add(b);
            (neighbors.TryGetValue(b, out var y) ? y : neighbors[b] = []).Add(a);
        }
        for (var i = 0; i < blocks.Count; i++)
        {
            var statements = blocks[i].Statements;
            foreach (var edge in ManagedValues.Edges(statements[^1]))
            {
                var after = liveIn[index[edge.Target]];
                var written = edge.Copies.Select(c => c.Target.Variable).ToHashSet();
                foreach (var copy in edge.Copies)
                    foreach (var other in after)
                        if (!(copy.Value is LocalValue source && source.Variable.Equals(other) && !written.Contains(other)))
                            Interfere(copy.Target.Variable, other);
            }
            var live = Out(i)!;
            var handling = Handling(i);
            foreach (var statement in statements.Reverse())
            {
                foreach (var defined in Definitions(statement))
                    foreach (var other in live)
                        if (!(statement is ManagedAssignment { Value: LocalValue source } && source.Variable.Equals(other)))
                            Interfere(defined.Variable, other);
                foreach (var defined in Definitions(statement)) live.Remove(defined.Variable);
                live.UnionWith(StatementUses(statement));
                live.UnionWith(handling);
            }
            if (caught.TryGetValue(i, out var exception))
                foreach (var other in live) Interfere(exception, other);
        }

        // 合并：沿复制按块序贪心，类之间以代表的邻接集判定冲突。
        var parent = new Dictionary<Variable, Variable>();
        Variable Find(Variable v)
        {
            while (parent.TryGetValue(v, out var p) && !p.Equals(v)) v = parent[v] = parent.TryGetValue(p, out var q) ? q : p;
            return v;
        }
        var fixedVariables = addressed.Concat(liveIn[0]).ToHashSet();
        var copies = blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Edges(s).SelectMany(e => e.Copies).Select(c => (c.Target, c.Value))
            .Concat(s is ManagedAssignment a ? [(a.Target, a.Value)] : []));
        var merged = false;
        foreach (var (target, value) in copies)
        {
            if (value is not LocalValue source || !target.Type.Equals(source.Type) || target.Width != source.Width) continue;
            if (fixedVariables.Contains(target.Variable) || fixedVariables.Contains(source.Variable)) continue;
            var (a, b) = (Find(target.Variable), Find(source.Variable));
            if (a.Equals(b) || neighbors.TryGetValue(a, out var adjacent) && adjacent.Contains(b)) continue;
            parent[b] = a;
            if (neighbors.Remove(b, out var moved))
            {
                var into = neighbors.TryGetValue(a, out var existing) ? existing : neighbors[a] = [];
                foreach (var n in moved)
                {
                    neighbors[n].Remove(b);
                    neighbors[n].Add(a);
                    into.Add(n);
                }
            }
            merged = true;
        }
        if (!merged) return body;

        LocalValue Rename(LocalValue local) => Find(local.Variable) is var root && !root.Equals(local.Variable) ? info[root] : local;
        ManagedValue Value(ManagedValue value) => value is LocalValue local ? Rename(local) : ManagedValues.Map(value, Value);
        bool Identity(LocalValue target, ManagedValue value) => value is LocalValue source && source.Variable.Equals(target.Variable);
        ManagedEdge Edge(ManagedEdge edge) => edge with
        {
            Copies = edge.Copies.Select(c => new ManagedCopy(Rename(c.Target), Value(c.Value))).Where(c => !Identity(c.Target, c.Value)).ToArray(),
        };
        IEnumerable<ManagedStatement> Statement(ManagedStatement statement)
        {
            var mapped = ManagedValues.MapEdges(ManagedValues.Map(statement, Value), Edge);
            mapped = mapped switch
            {
                ManagedAssignment a => a with { Target = Rename(a.Target) },
                ManagedCall { Result: { } result } c => c with { Result = Rename(result) },
                ManagedAwait { Result: { } result } w => w with { Result = Rename(result) },
                _ => mapped,
            };
            if (mapped is ManagedAssignment assignment && Identity(assignment.Target, assignment.Value)) yield break;
            yield return mapped;
        }
        return body with
        {
            Blocks = blocks.Select(b => b with { Statements = b.Statements.SelectMany(Statement).ToArray() }).ToArray(),
            Regions = body.Regions.Select(r => r.Exception is { } exception ? r with { Exception = Rename(exception) } : r).ToArray(),
        };
    }

    private static IEnumerable<LocalValue> Definitions(ManagedStatement statement) => statement switch
    {
        ManagedAssignment a => [a.Target],
        ManagedCall { Result: { } result } => [result],
        ManagedAwait { Result: { } result } => [result],
        _ => [],
    };

    private static IEnumerable<Variable> Uses(ManagedValue value) =>
        ManagedValues.Walk(value).OfType<LocalValue>().Select(l => l.Variable);

    /// <summary>语句读到的局部（不含赋值目标与边上的复制）。</summary>
    private static IEnumerable<Variable> StatementUses(ManagedStatement statement) =>
        (statement is ManagedAssignment a ? [a.Value] : ManagedValues.Of(statement)).SelectMany(Uses);
}
