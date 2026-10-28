using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>把状态分派中的捕获对象读取移到入口，保留连续的状态判断树。</summary>
internal static class SourceIteratorDispatch
{
    public static ManagedBody Rewrite(ManagedBody body)
    {
        var method = body.Method.Method;
        if (method.IsStatic || method.Parameters.Count != 0
            || !method.Owner.Interfaces.OfType<DefinitionRef>().Any(t => t.Definition.FullName == "System.Collections.IEnumerator")
            || !method.Owner.CustomAttributes.Any(a => a.Constructor.Owner.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute")) return body;
        if (method.Name.StartsWith("<>m__Finally", StringComparison.Ordinal)) return CleanupState(body);
        if (method.Name is "Dispose" or "System.IDisposable.Dispose") return SourceIteratorDispose.Rewrite(body);
        if (method.Name != "MoveNext") return body;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var state = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Where(a => a.Value is
            FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null, Field.Field.Name: "<>1__state" }).ToArray();
        if (state.Length != 1) return body;
        var variable = state[0].Target.Variable;
        bool State(ManagedValue value) => value is LocalValue local && local.Variable == variable;
        bool Test(ManagedValue value) => value is ComparisonValue comparison
            && (State(comparison.Left) && comparison.Right is ConstantValue || State(comparison.Right) && comparison.Left is ConstantValue);
        bool Capture(ManagedStatement statement) => statement is ManagedAssignment { Value: FieldValue
            { Receiver: ArgumentValue { Index: -1 }, Accessor: null, Field.Field.Name: "<>4__this" } field }
            && field.Field.Field.Owner == method.Owner;
        var dispatch = new HashSet<ulong>();
        var pending = new Stack<ulong>();
        pending.Push(body.Blocks[0].Address);
        while (pending.TryPop(out var address))
        {
            var block = blocks[address];
            if (dispatch.Contains(address) || block.Statements.Count == 0
                || block.Statements.SkipLast(1).Any(s => s != state[0] && !Capture(s))) continue;
            var last = block.Statements[^1];
            if (last is not ManagedJump && !(last is ManagedBranch branch && Test(branch.Condition))
                && !(last is ManagedSwitch selection && State(selection.Index))) continue;
            var edges = ManagedValues.Edges(last).ToArray();
            if (edges.Any(e => e.Copies.Count != 0)) continue;
            dispatch.Add(address);
            foreach (var edge in edges) pending.Push(edge.Target);
        }
        // 仅在分派树内提前读取非空状态机自身的捕获字段；不越过调用、写入或其他条件。
        var captures = body.Blocks.Where(b => dispatch.Contains(b.Address)).SelectMany(b => b.Statements).Where(Capture).Cast<ManagedAssignment>().ToArray();
        if (captures.Length == 0 || !dispatch.Any(a => blocks[a].Statements.Contains(state[0]))) return body;
        var targets = captures.Select(c => c.Target.Variable).Append(variable).ToHashSet();
        var incoming = body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges).GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Count());
        var definitions = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
        {
            ManagedAssignment a => new[] { a.Target.Variable },
            ManagedCall { Result: { } result } => [result.Variable],
            _ => Array.Empty<Variable>(),
        }).Concat(body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable));
        if (definitions.Where(targets.Contains).GroupBy(v => v).Any(g => g.Count() != 1)
            || dispatch.Any(address => incoming.GetValueOrDefault(address) > (address == body.Blocks[0].Address ? 0 : 1))
            || body.Blocks.Any(b => !dispatch.Contains(b.Address) && b.Statements.SelectMany(ManagedValues.Edges).Any(e => dispatch.Contains(e.Target)))) return body;
        var reordered = body with { Blocks = body.Blocks.Select((block, index) => block with
        {
            Statements = (index == 0 ? captures.Cast<ManagedStatement>() : []).Concat(block.Statements.Where(s => !captures.Contains(s))).ToArray(),
        }).ToArray() };
        return Switches(reordered, variable);
    }

    // 范围守卫加 switch 与逐状态等值判断等价；范围外仍返回 false，避免无符号守卫残留在 yield 方法中。
    private static ManagedBody Switches(ManagedBody body, Variable state)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var added = new List<(ManagedBlock Block, ulong Original)>();
        var next = blocks.Keys.Max() + 1;
        foreach (var block in body.Blocks)
        {
            if (block.Statements.LastOrDefault() is not ManagedBranch { Condition: ComparisonValue
                    { Condition: Cond.Ugt, Left: LocalValue index, Right: ConstantValue limit } condition } guard
                || index.Variable != state || index.Width != 32 || limit.Width != 32
                || guard.Taken.Copies.Count != 0 || guard.Fallthrough.Copies.Count != 0
                || blocks[guard.Taken.Target].Statements is not [ManagedReturn { Value: ConstantValue { Bits: 0 } }]
                || blocks[guard.Fallthrough.Target].Statements is not [ManagedSwitch selection]
                || selection.Index != index || selection.Cases.Count is 0 or > 64 || limit.Bits != (ulong)selection.Cases.Count - 1
                || selection.Cases.Any(e => e.Copies.Count != 0)
                || body.Regions.Any(r => r.Try.Contains(block.Address) != r.Try.Contains(guard.Fallthrough.Target)
                    || r.Handler.Contains(block.Address) != r.Handler.Contains(guard.Fallthrough.Target))) continue;
            var addresses = selection.Cases.Select((_, i) => i == 0 ? guard.Fallthrough.Target : next++).ToArray();
            blocks[block.Address] = block with { Statements = [.. block.Statements.SkipLast(1), new ManagedJump(guard.Address, guard.Fallthrough)] };
            for (var i = 0; i < addresses.Length; i++)
            {
                var test = new ComparisonValue(Cond.Eq, index, new ConstantValue((ulong)i, index.Type, 32), condition.Type);
                var branch = new ManagedBranch(selection.Address, test, selection.Cases[i],
                    i + 1 < addresses.Length ? new(addresses[i + 1], []) : guard.Taken);
                var decision = new ManagedBlock(addresses[i], [branch]);
                if (i == 0) blocks[decision.Address] = decision;
                else added.Add((decision, guard.Fallthrough.Target));
            }
        }
        return body with { Blocks = body.Blocks.Select(b => blocks[b.Address]).Concat(added.Select(p => p.Block)).ToArray(),
            Regions = body.Regions.Select(r => r with
            {
                Try = r.Try.Concat(added.Where(p => r.Try.Contains(p.Original)).Select(p => p.Block.Address)).ToArray(),
                Handler = r.Handler.Concat(added.Where(p => r.Handler.Contains(p.Original)).Select(p => p.Block.Address)).ToArray(),
            }).ToArray() };
    }

    // 清理入口先复位状态，再读取捕获资源。仅交换非空 this 的字段读取，不跨调用、分支或状态读取。
    private static ManagedBody CleanupState(ManagedBody body) => body with { Blocks = body.Blocks.Select(block =>
    {
        var prefix = block.Statements.TakeWhile(s => s is ManagedAssignment { Value: FieldValue
            { Receiver: ArgumentValue { Index: -1 }, Accessor: null } field }
            && field.Field.Field.Owner == body.Method.Method.Owner && field.Field.Field.Name != "<>1__state").Count();
        if (prefix == 0 || block.Statements.ElementAtOrDefault(prefix) is not ManagedStore
            { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null, Field.Field.Name: "<>1__state" } state,
                Value: ConstantValue { Width: 32, Bits: > int.MaxValue } } write
            || state.Field.Field.Owner != body.Method.Method.Owner) return block;
        return block with { Statements = [write, .. block.Statements.Take(prefix), .. block.Statements.Skip(prefix + 1)] };
    }).ToArray() };
}
