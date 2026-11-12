using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Structure;

public sealed record ExceptionEntryNormalization(NativeFunction Function, int Before, int After, ImmutableArray<string> Reasons);

/// <summary>把同子句表、封闭的无语句跳板收缩为最早的逻辑入口；合流直接取各展开边的值。</summary>
public static class ExceptionEntries
{
    public static bool SameClauses(HandlerEntry a, HandlerEntry b) => a.Clauses.Length == b.Clauses.Length &&
        a.Clauses.Zip(b.Clauses).All(p => p.First.Kind == p.Second.Kind && p.First.Selector == p.Second.Selector
            && p.First.TypeName == p.Second.TypeName && p.First.Matches.SequenceEqual(p.Second.Matches));

    public static ExceptionEntryNormalization Run(NativeFunction source)
    {
        int before = source.Blocks.Count(b => b.Handler is not null);
        if (before < 2) return new(source, before, before, []);
        var function = source;
        var reasons = new HashSet<string>();
        while (true)
        {
            reasons.Clear();
            var blocks = function.Blocks.ToDictionary(b => b.Identity);
            var handlers = function.Blocks.Where(b => b.Handler is not null).ToArray();
            var predecessors = blocks.Keys.ToDictionary(id => id, _ => new HashSet<BlockIdentity>());
            foreach (var b in function.Blocks)
                foreach (var to in SnapshotRewrite.Targets(b.End)) predecessors[to].Add(b.Identity);
            var paths = new Dictionary<BlockIdentity, Dictionary<BlockIdentity, ImmutableArray<BlockIdentity>>>();
            foreach (var h in handlers)
            {
                var path = new List<BlockIdentity>(); var seen = new HashSet<BlockIdentity>(); var cursor = h.Identity;
                while (seen.Add(cursor))
                {
                    path.Add(cursor);
                    if (!paths.TryGetValue(cursor, out var arrivals)) paths.Add(cursor, arrivals = []);
                    arrivals.Add(h.Identity, path.ToImmutableArray());
                    if (blocks[cursor].Statements.Length != 0 || blocks[cursor].End is not Jump jump) break;
                    cursor = jump.Target;
                }
            }
            bool changed = false;
            foreach (var (join, arrivals) in paths.Where(p => p.Value.Count > 1)
                .OrderByDescending(p => p.Value.Count).ThenBy(p => p.Value.Values.Sum(path => path.Length)))
            {
                var group = arrivals.Keys.ToHashSet();
                var first = blocks[group.First()].Handler!;
                if (group.Any(id => !SameClauses(first, blocks[id].Handler!)))
                { reasons.Add("子句表不同（种类、类型身份、选择值或次序）"); continue; }
                var corridor = arrivals.Values.SelectMany(p => p).ToHashSet();
                var removed = corridor.Where(id => id != join).ToHashSet();
                if (group.Any(id => blocks[id].Statements.Length != 0))
                { reasons.Add("入口或跳板有语句"); continue; }
                if (corridor.Any(id => predecessors[id].Any(p => !corridor.Contains(p)))
                    || function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                        .Any(c => c.Unwind is { } to && corridor.Contains(to) && !group.Contains(to)))
                { reasons.Add("汇合块或跳板有正常控制流前驱或组外处理入口"); continue; }
                var rewrite = new SnapshotRewrite(function);
                var exception = function.Terms.Atom(new ExceptionAtom(join), function.AddressWidth);
                var selector = function.Terms.Atom(new SelectorAtom(join), first.Selector.Width);
                var edges = function.Blocks.SelectMany(b => b.Statements.OfType<Call>()
                    .Where(c => c.Unwind is { } to && group.Contains(to)).Select(c => (From: b.Identity, Handler: c.Unwind!))).ToArray();
                var allMerges = corridor.SelectMany(id => blocks[id].Merges).ToArray();
                var transported = ImmutableArray.CreateBuilder<Merge>();
                foreach (var merge in allMerges)
                {
                    var owner = corridor.Single(id => blocks[id].Merges.Contains(merge));
                    var incoming = edges.Select(edge =>
                    {
                        var path = arrivals[edge.Handler];
                        Term value = merge.Result;
                        if (!path.Contains(owner)) value = function.Terms.Undefined(value.Width);
                        else for (int i = path.IndexOf(owner); i >= 0; i--)
                        {
                            var pred = i == 0 ? edge.From : path[i - 1];
                            var selected = blocks[path[i]].Merges.ToDictionary(m => m.Result,
                                m => m.Inputs.Single(v => v.Predecessor == pred).Value);
                            Term Map(Term t) => selected.TryGetValue(t, out var v) ? v : SnapshotRewrite.Rebuild(t, Map);
                            value = Map(value);
                        }
                        return new Incoming(edge.From, value);
                    }).ToImmutableArray();
                    if (incoming.Any(i => i.Value.Identity is ExceptionAtom) && incoming.All(i => i.Value.Kind == TermKind.Undefined || i.Value.Identity is ExceptionAtom a && group.Contains(a.Handler)))
                        rewrite.Replacements[merge.Result] = exception;
                    else if (incoming.Any(i => i.Value.Identity is SelectorAtom) && incoming.All(i => i.Value.Kind == TermKind.Undefined || i.Value.Identity is SelectorAtom a && group.Contains(a.Handler)))
                        rewrite.Replacements[merge.Result] = selector;
                    else transported.Add(merge with { Inputs = incoming });
                }
                foreach (var id in group)
                {
                    rewrite.Replacements[blocks[id].Handler!.Exception] = exception;
                    rewrite.Replacements[blocks[id].Handler!.Selector] = selector;
                }
                foreach (var b in function.Blocks)
                    rewrite.Blocks[b.Identity] = b with { Statements = b.Statements.Select(s => s is Call c && c.Unwind is { } to && group.Contains(to)
                        ? (Statement)(c with { Unwind = join }) : s).ToImmutableArray() };
                rewrite.Blocks[join] = rewrite.Blocks[join] with { Handler = new(exception, selector, first.Clauses), Merges = transported.ToImmutable() };
                rewrite.RemovedBlocks.UnionWith(removed);
                function = rewrite.Apply();
                changed = true; break;
            }
            if (!changed) break;
        }
        return new(function, before, function.Blocks.Count(b => b.Handler is not null), reasons.ToImmutableArray());
    }
}
