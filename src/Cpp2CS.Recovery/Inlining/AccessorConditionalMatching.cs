using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public sealed partial class AccessorQuery
{
    private sealed partial class ProgramQuery
    {
        private void Conditional(QueryContext c, Site anchor, MethodRef selected, AccessorConditional template,
            Dictionary<int, Term> fixedArgs, Site[] window, List<Site> sites, HashSet<Term> allTerms,
            Dictionary<BlockIdentity, Block> blocks, List<CandidateMatch> matches, HashSet<string> shapes)
        {
            var incoming = new IncomingValuesQuery(state); var facts = new PathFactQuery(state); var regions = new SnapshotRegionQuery(flow);
            var conditions = template.Paths.SelectMany(p => p.Conditions).Select(g => g.Value).Distinct().ToArray();
            var opportunities = new List<(Term Result, Site[] Window, AccessorRegion? Region)>();
            opportunities.AddRange(allTerms.Where(t => t.Operator is CoreOperator { Operation: CoreOperation.Select })
                .Select(t => (t, window, (AccessorRegion?)null)));
            foreach (var entry in blocks.Values.Where(b => b.End is Branch))
                foreach (var join in blocks.Values.Where(b => !b.Merges.IsEmpty && b.Identity != entry.Identity))
                {
                    var region = c.Get(regions, new(entry.Identity, join.Identity));
                    if (!region.IsSuccess || anchor.Point.Block != entry.Identity && !region.Value.Order.Contains(anchor.Point.Block)) continue;
                    var area = region.Value.Order.ToHashSet();
                    if (area.SelectMany(b => blocks[b].Statements).Any(s => s is not MemoryRead)) continue;
                    if (area.Append(entry.Identity).Count(b => blocks[b].End is Branch) != conditions.Length) continue;
                    int low = entry.Statements.Length;
                    while (low > 0 && Quiet(c, entry.Statements[low - 1], true)) low--;
                    if (anchor.Point.Block == entry.Identity && anchor.Point.Before < low) continue;
                    var available = sites.Where(s => area.Contains(s.Point.Block) || s.Point.Block == entry.Identity && s.Point.Before >= low).ToArray();
                    var ids = join.Merges.Select(m => m.Identity).ToHashSet();
                    foreach (var result in allTerms.Where(t => SnapshotRewrite.Dependencies([t]).Any(d => d.Identity is ResultAtom { Definition: MergeIdentity id } && ids.Contains(id))))
                        opportunities.Add((result, available, new(entry.Identity, join.Identity, region.Value.Order)));
                }
            foreach (var opportunity in opportunities)
            {
                if (new AccessorTerms(c.Snapshot.Terms, _ => null, (_, _) => null).Result(opportunity.Result) != opportunity.Result) continue;
                var possible = SnapshotRewrite.Dependencies([opportunity.Result]); possible.UnionWith(arguments.Keys);
                // 合流的来源也是发现实参的输入，实际代入仍逐路径复核。
                if (opportunity.Region is { } area)
                    foreach (var merge in blocks[area.Join].Merges) possible.UnionWith(SnapshotRewrite.Dependencies(merge.Inputs.Select(i => i.Value)));
                foreach (var binding in Bindings(c.Snapshot.Terms, selected, possible, fixedArgs))
                {
                    if (c.Step() is not null) return;
                    var reads = new List<Site>(); bool uncertain = false;
                    Term? Read(FieldRef field, Term? owner)
                    {
                        var found = ReadSites(opportunity.Window, selected, field, owner);
                        if (found.Length == 0 || found.Select(s => s.Value).Distinct().Count() != 1) { uncertain = true; return null; }
                        reads.AddRange(found); return found[0].Value;
                    }
                    var interpreter = new AccessorTerms(c.Snapshot.Terms, i => binding.GetValueOrDefault(i), Read);
                    var expected = template.Paths.Select(p => (Conditions: p.Conditions.Select(g => (Value: interpreter.Instantiate(g.Value), g.Positive)).ToArray(),
                        Value: interpreter.Instantiate(p.Value))).ToArray();
                    if (uncertain || expected.Any(p => p.Value is null || p.Conditions.Any(g => g.Value is null)) || !reads.Any(s => s.Identity == anchor.Identity)) continue;
                    bool matched;
                    if (opportunity.Region is null)
                    {
                        var actual = new List<(List<Term> Conditions, Term Value)>();
                        void Select(Term value, List<Term> guards)
                        {
                            if (value.Operator is CoreOperator { Operation: CoreOperation.Select })
                            {
                                Select(value.Operands[1], [.. guards, value.Operands[0]]);
                                Select(value.Operands[2], [.. guards, c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, value.Operands[0])]);
                            }
                            else actual.Add((guards, interpreter.Result(value)));
                        }
                        Select(opportunity.Result, []);
                        matched = actual.Count == expected.Length && actual.All(p => expected.Count(e => interpreter.Result(e.Value!) == p.Value
                            && e.Conditions.Select(g => g.Positive ? g.Value! : c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, g.Value!)).ToHashSet().SetEquals(p.Conditions)) == 1);
                    }
                    else
                    {
                        var region = opportunity.Region;
                        var inputs = c.Get(incoming, new(opportunity.Result, region.Join));
                        if (!inputs.IsSuccess || inputs.Value.IsEmpty) continue;
                        var expectedConditions = expected.SelectMany(p => p.Conditions).Select(g => g.Value!).Distinct().ToArray();
                        matched = region.Blocks.Append(region.Entry).Select(b => blocks[b].End).OfType<Branch>().All(b =>
                        {
                            var resolved = c.Get(state.Resolve, b.Condition);
                            return resolved.IsSuccess && expectedConditions.Any(t => t == resolved.Value
                                || c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, t) == resolved.Value);
                        });
                        var covered = new HashSet<int>();
                        foreach (var input in inputs.Value)
                        {
                            var cases = Enumerable.Range(0, expected.Length).Where(i => expected[i].Conditions.All(g =>
                                c.Get(facts, new(default, g.Value!, new FlowEdge(input.Predecessor, region.Join))) is { IsSuccess: true } fact
                                && fact.Value == (g.Positive ? PathTruth.True : PathTruth.False))).ToArray();
                            if (cases is not [var one] || interpreter.Result(input.Value) != interpreter.Result(expected[one].Value!)) { matched = false; break; }
                            covered.Add(one);
                        }
                        matched &= covered.Count == expected.Length;
                    }
                    if (!matched) continue;
                    reads = reads.DistinctBy(s => s.Identity).ToList();
                    var point = opportunity.Region is { } r ? new Point(r.Entry, blocks[r.Entry].Statements.Length) : reads.MinBy(s => s.Point.Before)!.Point;
                    var symbolic = Symbols(c.Snapshot.Terms, selected, fixedArgs, binding, template.Anchors, out var free);
                    var constraint = new AccessorTerms(c.Snapshot.Terms, i => symbolic.GetValueOrDefault(i), Read);
                    var equations = template.Paths.SelectMany(p => p.Conditions.Select(g => g.Value).Append(p.Value)).Select(constraint.Instantiate).OfType<Term>().ToArray();
                    reads = reads.DistinctBy(s => s.Identity).ToList();
                    Reason? placement = free.All(p => equations.Any(e => Determines(e, p))) ? Available(c, point, binding.Values, sites)
                        : new("inline.Accessor.Ambiguous", "条件模板形参的完整值没有可逆约束");
                    if (placement is null && opportunity.Region is { } regionAt)
                    {
                        var removed = regionAt.Blocks.ToHashSet(); var included = reads.Select(s => s.Identity).ToHashSet();
                        var escapingReads = sites.Where(s => !s.Write && (removed.Contains(s.Point.Block) || included.Contains(s.Identity))).Select(s => s.Value).ToHashSet();
                        var escapingMerges = removed.Append(regionAt.Join).SelectMany(b => blocks[b].Merges).Select(m => m.Identity).ToHashSet();
                        var outside = blocks.Values.Where(b => !removed.Contains(b.Identity)).SelectMany(b => b.Statements
                            .Where(s => s is not MemoryRead read || !included.Contains(read.Identity)).SelectMany(SnapshotRewrite.Uses)
                            .Concat(b.Identity == regionAt.Entry ? [] : SnapshotRewrite.Uses(b.End)));
                        var seen = new HashSet<Term>();
                        bool Escapes(Term value)
                        {
                            var resolved = c.Get(state.Resolve, value); if (!resolved.IsSuccess) return true;
                            value = resolved.Value;
                            if (value == opportunity.Result || !seen.Add(value)) return false;
                            if (escapingReads.Contains(value)) return true;
                            if (value.Identity is ResultAtom { Definition: MergeIdentity id } && escapingMerges.Contains(id)) return true;
                            return value.Operands.Any(Escapes);
                        }
                        if (outside.Any(Escapes)) placement = new("inline.Accessor.Placement", "条件区域的读取或其他出口值还有区域外使用");
                    }
                    else if (placement is null)
                        placement = Placement(c, blocks[point.Block], reads.ToArray(), point, binding, reads, opportunity.Result, sites);
                    var replacement = new AccessorReplacement(selected, selected.Method.IsStatic ? null : binding[-1],
                        Enumerable.Range(0, selected.Method.Parameters.Count).Select(i => binding[i]).ToArray(), opportunity.Result, point,
                        reads.Select(s => (ReadIdentity)s.Identity).ToArray(), []) { Region = opportunity.Region };
                    var coverage = SnapshotRewrite.Dependencies([opportunity.Result]); coverage.UnionWith(reads.Select(s => s.Value));
                    if (!matches.Any(m => m.Replacement.Method.Equals(selected) && m.Replacement.Result == replacement.Result
                        && m.Replacement.Arguments.SequenceEqual(replacement.Arguments) && m.Replacement.Receiver == replacement.Receiver))
                        matches.Add(new(replacement, coverage, placement));
                }
            }
            if (matches.Count == 0) shapes.Add("条件模板未匹配：条件或路径结果不等、区域含额外事件/出口，或分支已与调用方合并");
        }
    }
}
