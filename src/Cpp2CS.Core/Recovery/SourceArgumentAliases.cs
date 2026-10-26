using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>多条路径指向同一个 ref 参数时，消去仅搬运地址的局部副本。</summary>
internal static class SourceArgumentAliases
{
    public static ManagedBody Rewrite(ManagedBody body)
    {
        if (body.Blocks.Count == 0) return body;
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var writes = statements.OfType<ManagedAssignment>().Select(a => new ManagedCopy(a.Target, a.Value))
            .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies)).GroupBy(c => c.Target.Variable).ToDictionary(g => g.Key, g => g.ToArray());
        var blocked = statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable)
            .Concat(statements.OfType<ManagedAwait>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                .OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable)).ToHashSet();
        var aliases = new Dictionary<Variable, ArgumentValue>();
        foreach (var (variable, copies) in writes)
        {
            if (copies[0].Target.Type is not ByRefRef || blocked.Contains(variable)) continue;
            var pending = new Stack<ManagedValue>([copies[0].Target]);
            var seen = new HashSet<Variable>();
            var roots = new HashSet<ArgumentValue>();
            var valid = true;
            while (pending.TryPop(out var value))
            {
                if (value is ArgumentValue { Type: ByRefRef } argument) { roots.Add(argument); continue; }
                if (value is not LocalValue local || blocked.Contains(local.Variable) || !writes.TryGetValue(local.Variable, out var incoming))
                { valid = false; break; }
                if (!seen.Add(local.Variable)) continue;
                foreach (var copy in incoming) pending.Push(copy.Value);
            }
            if (valid && roots.ToArray() is [var root] && root.Type.Equals(copies[0].Target.Type)
                && !statements.OfType<ManagedStore>().Any(s => s.Target is ArgumentValue target && target.Index == root.Index)
                && seen.All(v => AssignedBeforeRead(body, v)))
                aliases[variable] = root;
        }
        if (aliases.Count == 0) return body;
        ManagedValue Map(ManagedValue value) => value is LocalValue local && aliases.TryGetValue(local.Variable, out var argument)
            ? argument : ManagedValues.Map(value, Map);
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements
            .Where(s => s is not ManagedAssignment a || !aliases.ContainsKey(a.Target.Variable))
            .Select(s => ManagedValues.MapEdges(ManagedValues.Map(s, Map, target => target), e => e with
                { Copies = e.Copies.Where(c => !aliases.ContainsKey(c.Target.Variable)).ToArray() })).ToArray() }).ToArray() };
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
