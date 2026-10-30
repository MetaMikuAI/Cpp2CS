using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>分离正常路径共用、但在 catch 中确定清理后重抛的有界路径。</summary>
internal static class SourceExceptionPaths
{
    internal static ManagedBody Rewrite(ManagedBody body)
    {
        if (body.Regions.Count == 0) return body;
        var separated = false;
        foreach (var index in Enumerable.Range(0, body.Regions.Count).OrderBy(i => body.Regions[i].Try.Count).ToArray())
        {
            var region = body.Regions[index];
            if (region.Kind != ManagedRegionKind.Catch || region.Exception is not { } exception) continue;
            var blocks = body.Blocks.ToDictionary(b => b.Address);
            var addressed = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).ToHashSet();
            if (addressed.Contains(exception) || body.Blocks.Where(b => !region.Handler.Contains(b.Address))
                .SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges)).Any(e => region.Handler.Contains(e.Target))
                || body.Regions.Where((_, i) => i != index).Any(r => region.Handler.Any(r.Try.Contains) && !region.Handler.All(r.Try.Contains)
                    || region.Handler.Any(r.Handler.Contains) && !region.Handler.All(r.Handler.Contains))) continue;
            var next = checked(blocks.Keys.Max() + 1);
            var cloned = new List<ManagedBlock>();
            var shared = false; var simplified = false;
            ulong? Visit(ulong address, HashSet<ManagedValue> aliases, HashSet<ulong> path)
            {
                if (cloned.Count >= 128 || path.Count >= 64 || path.Contains(address) || !blocks.TryGetValue(address, out var block)
                    || region.Try.Contains(address) || body.Regions.Where((_, i) => i != index).Any(r => r.Try.Contains(address) != r.Try.Contains(region.HandlerEntry)
                        || r.Handler.Contains(address) != r.Handler.Contains(region.HandlerEntry))) return null;
                shared |= !region.Handler.Contains(address);
                path = path.Append(address).ToHashSet(); aliases = aliases.ToHashSet();
                var resultAddress = next++; var slot = cloned.Count; cloned.Add(new ManagedBlock(resultAddress, []));
                var statements = new List<ManagedStatement>();
                ManagedValue Replace(ManagedValue value) => aliases.Contains(value) ? exception : ManagedValues.Map(value, Replace);
                ManagedEdge? Edge(ManagedEdge edge)
                {
                    if (edge.Copies.Any(c => c.Target == exception)) return null;
                    var incoming = aliases.ToHashSet();
                    foreach (var copy in edge.Copies) incoming.Remove(copy.Target);
                    foreach (var copy in edge.Copies)
                        if (aliases.Contains(copy.Value) && !addressed.Contains(copy.Target)) incoming.Add(copy.Target);
                    var target = Visit(edge.Target, incoming, path);
                    return target is null ? null : edge with { Target = target.Value, Copies = edge.Copies.Select(c => c with { Value = Replace(c.Value) }).ToArray() };
                }
                foreach (var statement in block.Statements)
                {
                    if (statement is ManagedThrow thrown)
                    {
                        if (!aliases.Contains(thrown.Exception)) return null;
                        statements.Add(thrown with { Exception = exception });
                    }
                    else if (statement is ManagedJump jump)
                    {
                        if (Edge(jump.Edge) is not { } edge) return null;
                        statements.Add(jump with { Edge = edge });
                    }
                    else if (statement is ManagedBranch branch)
                    {
                        bool? Known(ManagedValue value) => value is ComparisonValue { Condition: Cond.Eq or Cond.Ne } comparison
                            && (aliases.Contains(comparison.Left) && comparison.Right is ConstantValue { Bits: 0 }
                                || aliases.Contains(comparison.Right) && comparison.Left is ConstantValue { Bits: 0 })
                            ? comparison.Condition == Cond.Ne : null;
                        if (Known(branch.Condition) is { } taken)
                        {
                            if (Edge(taken ? branch.Taken : branch.Fallthrough) is not { } edge) return null;
                            statements.Add(new ManagedJump(branch.Address, edge)); simplified = true;
                        }
                        else
                        {
                            if (Edge(branch.Taken) is not { } takenEdge || Edge(branch.Fallthrough) is not { } otherEdge) return null;
                            statements.Add(branch with { Taken = takenEdge, Fallthrough = otherEdge });
                        }
                    }
                    else if (statement is ManagedAssignment or ManagedCall { Tail: false } or ManagedCheck)
                    {
                        statements.Add(ManagedValues.Map(statement, Replace, value => ManagedValues.Map(value, Replace)));
                        var target = statement switch { ManagedAssignment a => a.Target, ManagedCall c => c.Result, _ => null };
                        if (target is not null)
                        {
                            var copied = statement is ManagedAssignment copy && aliases.Contains(copy.Value);
                            aliases.Remove(target);
                            if (copied && !addressed.Contains(target)) aliases.Add(target);
                            if (target == exception) return null;
                        }
                    }
                    else return null;
                }
                if (statements.LastOrDefault() is not (ManagedJump or ManagedBranch or ManagedThrow)) return null;
                cloned[slot] = new ManagedBlock(resultAddress, statements);
                return resultAddress;
            }
            var entry = Visit(region.HandlerEntry, [exception], []);
            if (entry is null || !shared || !simplified) continue;
            var arranged = new List<ManagedBlock>();
            foreach (var block in body.Blocks)
            {
                if (block.Address == region.HandlerEntry) arranged.AddRange(cloned);
                if (!region.Handler.Contains(block.Address)) arranged.Add(block);
            }
            var cloneAddresses = cloned.Select(b => b.Address).ToHashSet();
            IReadOnlyList<ulong> Members(IReadOnlyList<ulong> original) => arranged.Select(b => b.Address)
                .Where(a => original.Contains(a) || original.Contains(region.HandlerEntry) && cloneAddresses.Contains(a)).ToArray();
            body = body with
            {
                Blocks = arranged,
                Regions = body.Regions.Select((r, i) => i == index
                ? r with { HandlerEntry = entry.Value, Handler = cloned.Select(b => b.Address).ToArray() }
                : r with { Try = Members(r.Try), Handler = Members(r.Handler) }).ToArray()
            };
            separated = true;
        }
        if (!separated) return body;
        body = Prune(body);
        var knownNull = SourceNonNullReceivers.ReadNull(body);
        var knownNonNull = SourceNonNullReceivers.Read(body, null);
        body = body with
        {
            Blocks = body.Blocks.Select(block => block with
            {
                Statements = block.Statements.Select(statement =>
        {
            if (statement is not ManagedBranch { Condition: ComparisonValue { Condition: Cond.Eq or Cond.Ne } condition } branch) return statement;
            bool Null(ManagedValue value, ManagedValue zero) => knownNull[statement].Contains(value) && zero is ConstantValue { Bits: 0 };
            bool Present(ManagedValue value, ManagedValue zero) => knownNonNull[statement].Contains(value) && zero is ConstantValue { Bits: 0 };
            if (Null(condition.Left, condition.Right) || Null(condition.Right, condition.Left))
                return new ManagedJump(branch.Address, condition.Condition == Cond.Eq ? branch.Taken : branch.Fallthrough);
            return Present(condition.Left, condition.Right) || Present(condition.Right, condition.Left)
                ? new ManagedJump(branch.Address, condition.Condition == Cond.Ne ? branch.Taken : branch.Fallthrough) : statement;
        }).ToArray()
            }).ToArray()
        };
        body = Prune(body);
        return SourceDeadLocals.Rewrite(body);
    }

    private static ManagedBody Prune(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var reached = new HashSet<ulong>(); var pending = new Queue<ulong>(); pending.Enqueue(body.Blocks[0].Address);
        while (true)
        {
            while (pending.TryDequeue(out var address))
                if (reached.Add(address))
                    foreach (var edge in blocks[address].Statements.SelectMany(ManagedValues.Edges)) pending.Enqueue(edge.Target);
            var handlers = body.Regions.Where(r => r.Try.Any(reached.Contains) && !reached.Contains(r.HandlerEntry)).Select(r => r.HandlerEntry).ToArray();
            if (handlers.Length == 0) break;
            foreach (var address in handlers) pending.Enqueue(address);
        }
        return body with
        {
            Blocks = body.Blocks.Where(b => reached.Contains(b.Address)).ToArray(),
            Regions = body.Regions.Where(r => r.Try.Any(reached.Contains)).Select(r => r with
            { Try = r.Try.Where(reached.Contains).ToArray(), Handler = r.Handler.Where(reached.Contains).ToArray() }).ToArray()
        };
    }
}
