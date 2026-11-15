using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Checks;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Recovery.Inlining;

public sealed partial class AccessorQuery
{
    private sealed partial class ProgramQuery
    {
        private sealed class CheckExitQuery(CheckQueries? checks) : Query<FlowEdge, bool>
        {
            public override Outcome<bool> Compute(QueryContext c, FlowEdge key)
            {
                if (checks is null) return Outcome<bool>.Success(false);
                var result = c.Get(checks.Checks, key);
                return result.IsSuccess ? Outcome<bool>.Success(result.Value is { CanAbsorb: true,
                    Exception: "System.NullReferenceException" or "System.IndexOutOfRangeException" }) : result.Propagate<bool>();
            }
        }
        private void EventConditional(QueryContext c, Site anchor, MethodRef selected, AccessorEventTemplate template,
            Dictionary<int, Term> fixedArgs, List<Site> sites, Dictionary<BlockIdentity, Block> blocks,
            List<CandidateMatch> matches, HashSet<string> shapes)
        {
            if (template.Paths.Any(p => p.Result is not null)) { shapes.Add("带事件条件模板：返回值尚未配对"); return; }
            var invoked = template.Paths.SelectMany(p => p.Events).OfType<AccessorInvocation>().Select(call => call.Method.Method).Distinct().ToArray();
            if (invoked.Any(method => calls is null || !calls.Values.Any(call => call.Method.Method == method)))
            { shapes.Add("带事件条件模板未匹配：缺少模板路径中的调用身份"); return; }
            foreach (var write in template.Paths.SelectMany(p => p.Events).OfType<AccessorFieldWrite>().Where(w => w.Value.Kind == TermKind.Constant))
            {
                var field = write.Field with { DeclaringType = selected.Concrete(write.Field.DeclaringType) };
                if (!sites.Any(s => s.Write && s.Field.Equals(field) && s.Receiver == anchor.Receiver && s.Value.ConstantValue == write.Value.ConstantValue))
                { shapes.Add("带事件条件模板未匹配：缺少字段的常量写入"); return; }
            }
            var exits = new CheckExitQuery(checks); var pathsQuery = new SnapshotPathsQuery(new FlowQueries(false), exits);
            var regionQuery = new SnapshotRegionQuery(new FlowQueries(false), exits);
            var templateFields = template.Anchors.OfType<FieldValue>().Select(f => f.Field.Field).ToHashSet();
            foreach (var entry in blocks.Values.Where(b => b.Identity == anchor.Point.Block || b.End is Branch))
            {
                if (c.Get(flow.Dominates, new(entry.Identity, anchor.Point.Block)) is not { IsSuccess: true, Value: true }) continue;
                var starts = sites.Where(s => s.Point.Block == entry.Identity && s.Receiver == anchor.Receiver && templateFields.Contains(s.Field.Field)).Select(s => s.Point.Before).Distinct().ToArray();
                if (starts.Length == 0) continue;
                foreach (var join in blocks.Values.Where(b => b.Identity != entry.Identity))
                {
                    var area = c.Get(regionQuery, new(entry.Identity, join.Identity));
                    if (!area.IsSuccess || anchor.Point.Block != entry.Identity && !area.Value.Order.Contains(anchor.Point.Block)) continue;
                    foreach (int start in starts)
                    {
                        if (anchor.Point.Block == entry.Identity && anchor.Point.Before < start) continue;
                        var point = new Point(entry.Identity, start);
                        var paths = c.Get(pathsQuery, new(point, join.Identity));
                        if (!paths.IsSuccess || paths.Value.Length != template.Paths.Count) continue;
                        var points = paths.Value.SelectMany(p => p.Points).ToHashSet();
                        if (points.Any(p => blocks[p.Block].Statements[p.Before] is Call { Unwind: not null } or Call { DoesNotReturn: true } or MemoryRead { Acquire: true })) continue;
                        // 被排除的检查失败出口必须由区域内的访问吸收：区域换成调用后由这次调用对接收者的判空承接。吸收点在区域外的检查不能随区域消失。
                        bool absorbedInside = true;
                        foreach (var edge in paths.Value.SelectMany(p => p.Edges).Distinct())
                        {
                            if (blocks[edge.Source].End is not Branch gate) continue;
                            var failure = new FlowEdge(edge.Source, gate.True == edge.Target ? gate.False : gate.True);
                            if (c.Get(exits, failure) is not { IsSuccess: true, Value: true }) continue;
                            if (checks is null || c.Get(checks.Checks, failure) is not { IsSuccess: true, Value: { } check }
                                || !check.Accesses.All(points.Contains)) { absorbedInside = false; break; }
                        }
                        if (!absorbedInside) continue;
                        var window = sites.Where(s => points.Contains(s.Point)).ToArray();
                        var roots = points.SelectMany(p => SnapshotRewrite.Uses(blocks[p.Block].Statements[p.Before]))
                            .Concat(paths.Value.SelectMany(p => p.Edges).Select(e => blocks[e.Source].End).OfType<Branch>().Select(b => b.Condition));
                        var possible = new HashSet<Term>(arguments.Keys);
                        foreach (var root in roots)
                            if (c.Get(state.Resolve, root) is { IsSuccess: true } value) possible.UnionWith(SnapshotRewrite.Dependencies([value.Value]));
                        foreach (var binding in Bindings(c.Snapshot.Terms, selected, possible, fixedArgs))
                        {
                            if (c.Step() is not null) return;
                            var reads = new HashSet<ReadIdentity>(); bool uncertain = false;
                            Term? Read(FieldRef field, Term? receiver)
                            {
                                var found = ReadSites(window, selected, field, receiver);
                                if (found.Length == 0 || found.Select(s => s.Value).Distinct().Count() != 1) { uncertain = true; return null; }
                                reads.UnionWith(found.Select(s => (ReadIdentity)s.Identity)); return found[0].Value;
                            }
                            var interpreter = new AccessorTerms(c.Snapshot.Terms, i => binding.GetValueOrDefault(i), Read);
                            AccessorEvent? Instantiate(AccessorEvent effect) => effect switch
                            {
                                AccessorFieldWrite w when interpreter.Instantiate(w.Receiver) is { } r && interpreter.Instantiate(w.Value) is { } v =>
                                    new AccessorFieldWrite(w.Field with { DeclaringType = selected.Concrete(w.Field.DeclaringType) }, r, v),
                                AccessorInvocation call => InstantiateCall(call), _ => null,
                            };
                            AccessorInvocation? InstantiateCall(AccessorInvocation call)
                            {
                                var args = call.Arguments.Select(interpreter.Instantiate).ToArray();
                                var receiver = call.Receiver is null ? null : interpreter.Instantiate(call.Receiver);
                                if (args.Any(a => a is null) || call.Receiver is not null && receiver is null) return null;
                                return new(new(call.Method.Method, call.Method.TypeArguments.Select(selected.Concrete).ToArray(), call.Method.MethodArguments.Select(selected.Concrete).ToArray()),
                                    call.Virtual, receiver, args.OfType<Term>().ToArray());
                            }
                            var expected = template.Paths.Select(p => (Conditions: p.Conditions.Select(g => (Value: interpreter.Instantiate(g.Value), g.Positive)).ToArray(),
                                Events: p.Events.Select(Instantiate).ToArray())).ToArray();
                            if (uncertain || expected.Any(p => p.Conditions.Any(g => g.Value is null) || p.Events.Any(e => e is null))) continue;
                            var used = new HashSet<int>(); bool matched = true;
                            foreach (var path in paths.Value)
                            {
                                var conditions = new List<Term>();
                                foreach (var edge in path.Edges.Where(e => blocks[e.Source].End is Branch))
                                {
                                    var b = (Branch)blocks[edge.Source].End;
                                    if (c.Get(exits, new(edge.Source, b.True == edge.Target ? b.False : b.True)) is { IsSuccess: true, Value: true }) continue;
                                    if (c.Get(state.Resolve, b.Condition) is not { IsSuccess: true } condition) { matched = false; break; }
                                    conditions.Add(b.True == edge.Target ? condition.Value : c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, condition.Value));
                                }
                                var candidates = Enumerable.Range(0, expected.Length).Where(i => expected[i].Conditions.Select(g => g.Positive ? g.Value! : c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, g.Value!)).ToHashSet().SetEquals(conditions)).ToArray();
                                if (!matched || candidates is not [var one] || !used.Add(one)) { matched = false; break; }
                                bool called = false; var priorWrites = new List<MemoryWrite>();
                                foreach (var p in path.Points)
                                {
                                    var statement = blocks[p.Block].Statements[p.Before];
                                    if (statement is MemoryRead read)
                                    {
                                        if (called) { matched = false; break; }
                                        var readLocation = c.Get(state.Locations, new(read.Address, read.Width));
                                        foreach (var write in priorWrites)
                                        {
                                            var writeLocation = c.Get(state.Locations, new(write.Address, write.Width));
                                            if (!readLocation.IsSuccess || !writeLocation.IsSuccess
                                                || c.Get(state.Alias, new(readLocation.Value, writeLocation.Value)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint })
                                            { matched = false; break; }
                                        }
                                    }
                                    if (statement is MemoryWrite writeAt) priorWrites.Add(writeAt);
                                    called |= statement is Call;
                                }
                                if (!matched) break;
                                var events = path.Points.Where(p => blocks[p.Block].Statements[p.Before] is not MemoryRead).ToArray();
                                if (events.Length != expected[one].Events.Length) { matched = false; break; }
                                for (int i = 0; i < events.Length; i++)
                                    if (!EventEquals(c, blocks[events[i].Block].Statements[events[i].Before], events[i], expected[one].Events[i]!)) { matched = false; break; }
                                if (!matched) break;
                            }
                            if (!matched || used.Count != expected.Length || !window.Any(s => s.Identity == anchor.Identity)) continue;
                            // 所有读取必须是模板纯项；不能留下未解释的堆访问。
                            if (points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<MemoryRead>().Any(r => !reads.Contains(r.Identity))) continue;
                            if (points.Where(p => p.Block == entry.Identity).Any(p => blocks[p.Block].Statements[p.Before] is Call)) continue;
                            var symbolic = Symbols(c.Snapshot.Terms, selected, fixedArgs, binding, template.Anchors, out var free);
                            var constraint = new AccessorTerms(c.Snapshot.Terms, i => symbolic.GetValueOrDefault(i), Read);
                            IEnumerable<Term> Inputs(AccessorEvent effect) => effect switch
                            {
                                AccessorFieldWrite w => [w.Receiver, w.Value],
                                AccessorInvocation call => call.Arguments.Concat(call.Receiver is { } receiver ? [receiver] : []), _ => [],
                            };
                            var equations = template.Paths.SelectMany(p => p.Conditions.Select(g => g.Value).Concat(p.Events.SelectMany(Inputs)))
                                .Select(constraint.Instantiate).OfType<Term>().ToArray();
                            Reason? placement = free.All(p => equations.Any(e => Determines(e, p))) ? Available(c, point, binding.Values, sites)
                                : new("inline.Accessor.Ambiguous", "带事件条件模板的形参没有完整可逆约束");
                            var outside = blocks.Values.SelectMany(b => b.Statements.Select((s, i) => (s, p: new Point(b.Identity, i)))
                                .Where(x => !points.Contains(x.p)).SelectMany(x => SnapshotRewrite.Uses(x.s))
                                .Concat(area.Value.Order.Append(entry.Identity).Contains(b.Identity) ? [] : SnapshotRewrite.Uses(b.End)));
                            var coveredValues = window.Where(s => !s.Write).Select(s => s.Value).ToHashSet();
                            var removedDefinitions = points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<Call>().Select(call => (StableIdentity)call.Identity)
                                .Concat(area.Value.Order.Append(join.Identity).SelectMany(id => blocks[id].Merges.Select(merge => merge.Identity))).ToHashSet();
                            var seen = new HashSet<Term>();
                            bool Escapes(Term term)
                            {
                                var value = c.Get(state.Resolve, term); if (!value.IsSuccess) return true;
                                if (!seen.Add(value.Value)) return false;
                                return coveredValues.Contains(value.Value)
                                    || value.Value.Identity is ResultAtom atom && removedDefinitions.Contains(atom.Definition)
                                    || value.Value.Identity is MemoryMerge merge && area.Value.Order.Contains(merge.Block)
                                    || value.Value.Operands.Any(Escapes);
                            }
                            if (outside.Any(Escapes)) placement = new("inline.Accessor.Placement", "区域内读到的字段值在区域外另有使用");
                            var replacement = new AccessorReplacement(selected, selected.Method.IsStatic ? null : binding[-1],
                                Enumerable.Range(0, selected.Method.Parameters.Count).Select(i => binding[i]).ToArray(), null, point, reads.ToArray(),
                                points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<MemoryWrite>().Select(w => w.Identity).ToArray())
                                { Region = new(entry.Identity, join.Identity, area.Value.Order) };
                            var coverage = SnapshotRewrite.Dependencies(roots.Select(r => c.Get(state.Resolve, r)).Where(v => v.IsSuccess).Select(v => v.Value));
                            if (!matches.Any(m => m.Replacement.Method.Equals(selected) && m.Replacement.Point == point && m.Replacement.Region?.Join == join.Identity
                                && m.Replacement.Arguments.SequenceEqual(replacement.Arguments) && m.Replacement.Receiver == replacement.Receiver))
                                matches.Add(new(replacement, coverage, placement));
                        }
                    }
                }
            }
            if (matches.Count == 0) shapes.Add("带事件条件模板未匹配：路径条件、事件、纯项覆盖或区域边界不成立");
        }
        private bool EventEquals(QueryContext c, Statement actual, Point point, AccessorEvent expected)
        {
            Term? Resolve(Term term) => c.Get(state.Resolve, term) is { IsSuccess: true } value ? value.Value : null;
            if (actual is MemoryWrite { Release: false } write && Resolve(write.Value) is { } value
                && c.Get(locations, new(write.Address, write.Width)) is { IsSuccess: true } at)
            {
                var views = at.Value.Views.Where(v => v.Offset == 0 && types.Size(v.Type) * 8 == write.Width).ToArray();
                if (views is not [var view]) return false;
                if (expected is AccessorFieldWrite field) return view.Kind == ManagedLocationKind.InstanceField && view.Path.Length == 1
                    && view.Path[0].Equals(field.Field) && Resolve(view.Root) == field.Receiver && value == field.Value;
            }
            if (actual is Call { Unwind: null } call && expected is AccessorInvocation invocation && calls?.GetValueOrDefault(call.Identity) is { } target)
            {
                if (!target.Method.Equals(invocation.Method) || target.Virtual != invocation.Virtual) return false;
                var source = new BoundSourceQuery(state);
                Term? Input(BoundValue? input) => input?.Source is { } bound && c.Get(source, new(bound, point)) is { IsSuccess: true } value ? Resolve(value.Value) : null;
                return target.Binding.Parameters.Select(Input).SequenceEqual(invocation.Arguments.Cast<Term?>()) && Input(target.Binding.This) == invocation.Receiver;
            }
            return false;
        }
    }
}
