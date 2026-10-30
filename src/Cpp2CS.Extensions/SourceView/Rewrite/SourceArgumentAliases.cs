using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>多条路径指向同一个参数或局部存储时，消去仅搬运地址的局部副本。</summary>
internal static class SourceArgumentAliases
{
    public static ManagedBody Rewrite(ManagedBody body)
    {
        if (body.Blocks.Count == 0) return body;
        body = SplitStores(body);
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var writes = statements.OfType<ManagedAssignment>().Select(a => new ManagedCopy(a.Target, a.Value))
            .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies)).GroupBy(c => c.Target.Variable).ToDictionary(g => g.Key, g => g.ToArray());
        var blocked = statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable)
            .Concat(statements.OfType<ManagedAwait>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                .OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable)).ToHashSet();
        var aliases = new Dictionary<Variable, ManagedValue>();
        foreach (var (variable, copies) in writes)
        {
            if (copies[0].Target.Type is not ByRefRef || blocked.Contains(variable)) continue;
            var pending = new Stack<ManagedValue>([copies[0].Target]);
            var seen = new HashSet<Variable>();
            var roots = new HashSet<ManagedValue>();
            var valid = true;
            while (pending.TryPop(out var value))
            {
                if (value is ArgumentValue { Type: ByRefRef } argument) { roots.Add(argument); continue; }
                if (value is AddressValue { Target: LocalValue { Type: not ByRefRef } }) { roots.Add(value); continue; }
                if (value is not LocalValue local || blocked.Contains(local.Variable) || !writes.TryGetValue(local.Variable, out var incoming))
                { valid = false; break; }
                if (!seen.Add(local.Variable)) continue;
                foreach (var copy in incoming) pending.Push(copy.Value);
            }
            if (valid && roots.ToArray() is [var root] && root.Type.Equals(copies[0].Target.Type)
                && (root is not ArgumentValue parameter || !statements.OfType<ManagedStore>().Any(s => s.Target is ArgumentValue target && target.Index == parameter.Index))
                && seen.All(v => AssignedBeforeRead(body, v)))
                aliases[variable] = root;
        }
        if (aliases.Count == 0) return body;
        ManagedValue Map(ManagedValue value) => value is LocalValue local && aliases.TryGetValue(local.Variable, out var argument)
            ? argument : ManagedValues.Map(value, Map);
        return body with
        {
            Blocks = body.Blocks.Select(b => b with
            {
                Statements = b.Statements
            .Where(s => s is not ManagedAssignment a || !aliases.ContainsKey(a.Target.Variable))
            .Select(s => ManagedValues.MapEdges(ManagedValues.Map(s, Map, target => ManagedValues.Map(target, Map)), e => e with
            { Copies = e.Copies.Where(c => !aliases.ContainsKey(c.Target.Variable)).ToArray() })).ToArray()
            }).ToArray()
        };
    }

    // 只用一次的 ref 汇合可沿入边分别写入；仍使用原位置求得的地址，不重算字段读取。
    private static ManagedBody SplitStores(ManagedBody body)
    {
        foreach (var block in body.Blocks.ToArray())
        {
            if (block == body.Blocks[0] || body.Regions.Any(r => r.HandlerEntry == block.Address)
                || block.Statements is not [ManagedStore { Target: IndirectValue { Address: LocalValue { Type: ByRefRef } pointer } }, ManagedReturn]) continue;
            var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
            if (statements.SelectMany(s => (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Count(l => l.Variable == pointer.Variable) != 1
                || statements.OfType<ManagedAssignment>().Any(a => a.Target.Variable == pointer.Variable)) continue;
            var incoming = statements.SelectMany(ManagedValues.Edges).Where(e => e.Target == block.Address).ToArray();
            if (incoming.Length < 2 || incoming.Any(e => e.Copies.Count(c => c.Target.Variable == pointer.Variable) != 1
                || e.Copies.Single(c => c.Target.Variable == pointer.Variable).Value is not LocalValue { Type: ByRefRef })) continue;
            var next = body.Blocks.Max(b => b.Address) + 1;
            var copies = new List<ManagedBlock>();
            var edges = new Dictionary<ManagedEdge, ManagedEdge>(ReferenceEqualityComparer.Instance);
            foreach (var edge in incoming)
            {
                var value = edge.Copies.Single(c => c.Target.Variable == pointer.Variable).Value;
                if (edge.Copies.Any(c => ManagedValues.Walk(value).OfType<LocalValue>().Any(l => l.Variable == c.Target.Variable))) break;
                ManagedValue Replace(ManagedValue v) => v is LocalValue local && local.Variable == pointer.Variable ? value : ManagedValues.Map(v, Replace);
                copies.Add(new(next, block.Statements.Select(s => ManagedValues.Map(s, Replace)).ToArray()));
                edges[edge] = new(next++, edge.Copies.Where(c => c.Target.Variable != pointer.Variable).ToArray());
            }
            if (copies.Count != incoming.Length) continue;
            body = body with
            {
                Blocks = body.Blocks.Where(b => b != block).Select(b => b with
                { Statements = b.Statements.Select(s => ManagedValues.MapEdges(s, e => edges.GetValueOrDefault(e, e))).ToArray() }).Concat(copies).ToArray(),
                Regions = body.Regions.Select(r => r with
                {
                    Try = r.Try.SelectMany(a => a == block.Address ? copies.Select(b => b.Address) : [a]).ToArray(),
                    Handler = r.Handler.SelectMany(a => a == block.Address ? copies.Select(b => b.Address) : [a]).ToArray(),
                }).ToArray(),
            };
        }
        return body;
    }

    // 只走尚未定义的路径；异常入口从受保护块入口出发，宁可保留块内才赋值的副本。
    private static bool AssignedBeforeRead(ManagedBody body, Variable variable)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var handlers = body.Regions.SelectMany(r => r.Try.Select(a => (Address: a, r.HandlerEntry))).ToLookup(p => p.Address, p => p.HandlerEntry);
        var pending = new Stack<ulong>([body.Blocks[0].Address]);
        var seen = new HashSet<ulong>();
        bool Reads(ManagedValue value) => ManagedValues.Walk(value).OfType<LocalValue>().Any(l => l.Variable == variable);
        while (pending.TryPop(out var address))
        {
            if (!seen.Add(address) || !blocks.TryGetValue(address, out var block)) continue;
            foreach (var handler in handlers[address]) pending.Push(handler);
            foreach (var statement in block.Statements)
            {
                var operands = statement is ManagedAssignment a ? [a.Value] : ManagedValues.Of(statement);
                if (operands.Concat(ManagedValues.CopiedValues(statement)).Any(Reads)) return false;
                if (statement is ManagedAssignment assignment && assignment.Target.Variable == variable) break;
                foreach (var edge in ManagedValues.Edges(statement))
                    if (!edge.Copies.Any(c => c.Target.Variable == variable)) pending.Push(edge.Target);
            }
        }
        return true;
    }
}
