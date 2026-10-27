namespace Cpp2CS.Recovery;

/// <summary>把仅由 catch 到达的后续块归回 handler，保持其他异常区域和所有正常入边。</summary>
internal static class SourceCatchHandlers
{
    internal static ManagedBody Rewrite(ManagedBody body)
    {
        if (body.Regions.Count == 0 || body.Blocks.Any(b => b.Statements.LastOrDefault() is not
            (ManagedJump or ManagedBranch or ManagedSwitch or ManagedReturn or ManagedThrow or ManagedRethrow or ManagedEndFault))) return body;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var incoming = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (e.Target, b.Address)))
            .GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Select(e => e.Address).Distinct().ToArray());
        var order = body.Blocks.Select(b => b.Address).ToList();
        var regions = body.Regions.ToArray();
        foreach (var index in Enumerable.Range(0, regions.Length).OrderBy(i => regions[i].Try.Count + regions[i].Handler.Count))
        {
            var region = regions[index];
            if (region.Kind != ManagedRegionKind.Catch) continue;
            var handler = region.Handler.ToHashSet();
            bool changed;
            do
            {
                changed = false;
                var next = handler.SelectMany(a => blocks[a].Statements.SelectMany(ManagedValues.Edges)).Select(e => e.Target).Distinct().ToArray();
                foreach (var target in next)
                {
                    if (handler.Contains(target) || target == body.Blocks[0].Address || region.Try.Contains(target)
                        || incoming[target].Any(p => !handler.Contains(p))
                        || regions.Where((_, i) => i != index).Any(r => r.Try.Contains(target) != r.Try.Contains(region.HandlerEntry)
                            || r.Handler.Contains(target) != r.Handler.Contains(region.HandlerEntry))) continue;
                    changed |= handler.Add(target);
                }
            } while (changed);
            if (handler.Count == region.Handler.Count) continue;
            var added = order.Where(a => handler.Contains(a) && !region.Handler.Contains(a)).ToArray();
            var arranged = order.Except(added).ToList();
            arranged.InsertRange(arranged.FindLastIndex(region.Handler.Contains) + 1, added);
            var positions = arranged.Select((a, i) => (a, i)).ToDictionary(p => p.a, p => p.i);
            bool Contiguous(IEnumerable<ulong> members)
            {
                var indices = members.Select(a => positions[a]).ToArray();
                return indices.Length > 0 && indices.Max() - indices.Min() + 1 == indices.Length;
            }
            if (!Contiguous(handler) || regions.Where((_, i) => i != index).Any(r => !Contiguous(r.Try) || !Contiguous(r.Handler))
                || !Contiguous(region.Try)) continue;
            order = arranged;
            regions[index] = region with { Handler = order.Where(handler.Contains).ToArray() };
        }
        return body with
        {
            Blocks = order.Select(a => blocks[a]).ToArray(),
            Regions = regions.Select(r => r with { Try = order.Where(r.Try.Contains).ToArray(), Handler = order.Where(r.Handler.Contains).ToArray() }).ToArray(),
        };
    }
}
