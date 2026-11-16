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
                return result.IsSuccess ? Outcome<bool>.Success(result.Value is { Kind: not null }) : result.Propagate<bool>();
            }
        }
        private void EventConditional(QueryContext c, Site anchor, MethodRef selected, AccessorEventTemplate template,
            Dictionary<int, Term> fixedArgs, List<Site> sites, Dictionary<BlockIdentity, Block> blocks,
            List<CandidateMatch> matches, HashSet<string> shapes)
        {
            // 负的阶段是区域成立之前的原因：候选的续点多数本来就不对，只在没有更靠后的原因时才报。
            int reached = -4; string? detail = null;
            void Unmatched(int stage, string why) { if (stage >= reached) { reached = stage; detail = why; } }
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
                foreach (var join in blocks.Keys.Where(id => id != entry.Identity).Cast<BlockIdentity?>().Append(null))
                {
                    // 已有可放置的公共续点时保留该区域；返回续点只补充尚无解释的现场。
                    if (join is null && matches.Any(m => m.Placement is null && m.Replacement.Method.Equals(selected))) continue;
                    var area = c.Get(regionQuery, new(entry.Identity, join));
                    if (!area.IsSuccess || anchor.Point.Block != entry.Identity && !area.Value.Order.Contains(anchor.Point.Block)) continue;
                    foreach (int start in starts)
                    {
                        if (anchor.Point.Block == entry.Identity && anchor.Point.Before < start) continue;
                        var point = new Point(entry.Identity, start);
                        var paths = c.Get(pathsQuery, new(point, join));
                        if (!paths.IsSuccess) continue;
                        if (paths.Value.Length != template.Paths.Count) { Unmatched(-3, "区域的路径数与模板不同"); continue; }
                        IReadOnlyList<Term> returned = []; Return? returnEnd = null;
                        if (join is null)
                        {
                            var values = paths.Value.Select(p => p.ReturnBlock is { } block && returnValues is not null
                                ? c.Get(returnValues, block) : Outcome<IReadOnlyList<Term>>.Failure(new("inline.Accessor.Return", "没有签名返回项查询"))).ToArray();
                            if (values.Any(v => !v.IsSuccess)) { Unmatched(0, "签名返回值未能按项确定"); continue; }
                            returned = values[0].Value;
                            if (values.Skip(1).Any(v => !v.Value.SequenceEqual(returned))) { Unmatched(0, "各返回路径的签名返回值不同"); continue; }
                            returnEnd = (Return)blocks[paths.Value[0].ReturnBlock!].End;
                        }
                        var points = paths.Value.SelectMany(p => p.Points).ToHashSet();
                        if (points.Any(p => blocks[p.Block].Statements[p.Before] is Call { Unwind: not null })) { Unmatched(-2, "区域内的调用带展开边"); continue; }
                        if (points.Any(p => blocks[p.Block].Statements[p.Before] is Call { DoesNotReturn: true } or MemoryRead { Acquire: true })) { Unmatched(-2, "区域内有不返回的调用或获取语义的读取"); continue; }
                        var regionChecks = paths.Value.SelectMany(p => p.Edges).Distinct().Select(edge =>
                        {
                            if (blocks[edge.Source].End is not Branch gate) return null;
                            var failure = new FlowEdge(edge.Source, gate.True == edge.Target ? gate.False : gate.True);
                            return checks is not null && c.Get(exits, failure) is { IsSuccess: true, Value: true }
                                && c.Get(checks.Checks, failure) is { IsSuccess: true, Value: { } check } ? check : null;
                        }).OfType<ConditionalCheck>().Distinct().ToArray();
                        if (regionChecks.Any(check => check.CanAbsorb && !check.Accesses.All(points.Contains))) { Unmatched(-1, "被吸收的检查有访问点在区域外"); continue; }
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
                            Term? Length(Term array, int width)
                            {
                                var found = points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<MemoryRead>()
                                    .Where(r => c.Get(locations, new(r.Address, r.Width)) is { IsSuccess: true } at
                                        && at.Value.Views is [ { Kind: ManagedLocationKind.ArrayLength } view ]
                                        && c.Get(state.Resolve, view.Root) is { IsSuccess: true } root && root.Value == array).ToArray();
                                var values = found.Select(r => c.Get(state.Read, r.Identity)).ToArray();
                                if (values.Length == 0 || values.Any(v => !v.IsSuccess) || values.Select(v => v.Value).Distinct().Count() != 1) return null;
                                reads.UnionWith(found.Select(r => r.Identity));
                                return new AccessorTerms(c.Snapshot.Terms, _ => null, (_, _) => null).Resize(values[0].Value, width);
                            }
                            var interpreter = new AccessorTerms(c.Snapshot.Terms, i => binding.GetValueOrDefault(i), Read, arrayLength: Length);
                            AccessorEvent? Instantiate(AccessorEvent effect) => effect switch
                            {
                                AccessorFieldWrite w when interpreter.Instantiate(w.Receiver) is { } r && interpreter.Instantiate(w.Value) is { } v =>
                                    new AccessorFieldWrite(w.Field with { DeclaringType = selected.Concrete(w.Field.DeclaringType) }, r, v),
                                AccessorArrayWrite w when interpreter.Instantiate(w.Array) is { } a && interpreter.Instantiate(w.Index) is { } i && interpreter.Instantiate(w.Value) is { } v => new AccessorArrayWrite(a, i, interpreter.Resize(v, types.StorageBits(selected.Concrete(w.ElementType))), selected.Concrete(w.ElementType)),
                                AccessorCheck check => InstantiateCheck(check),
                                AccessorInvocation call => InstantiateCall(call), _ => null,
                            };
                            AccessorCheck? InstantiateCheck(AccessorCheck check)
                            {
                                var inputs = check.Inputs.Select(i => (i.Role, Value: interpreter.Instantiate(i.Value))).ToArray();
                                return inputs.Any(i => i.Value is null) || interpreter.Instantiate(check.FailureCondition) is not { } condition ? null
                                    : new(check.Kind, inputs.Select(i => new AccessorCheckInput(i.Role, i.Value!)).ToArray(), condition);
                            }
                            AccessorInvocation? InstantiateCall(AccessorInvocation call)
                            {
                                var args = call.Arguments.Select(interpreter.Instantiate).ToArray();
                                var receiver = call.Receiver is null ? null : interpreter.Instantiate(call.Receiver);
                                if (args.Any(a => a is null) || call.Receiver is not null && receiver is null) return null;
                                var method = new MethodRef(call.Method.Method, call.Method.TypeArguments.Select(selected.Concrete).ToArray(), call.Method.MethodArguments.Select(selected.Concrete).ToArray());
                                return new(method, call.Virtual, receiver, args.Select((a, i) => interpreter.Resize(a!, types.StorageBits(method.Concrete(method.Method.Parameters[i].Type)))).ToArray());
                            }
                            var expected = template.Paths.Select(p => (Conditions: p.Conditions.Select(g => (Value: interpreter.Instantiate(g.Value), g.Positive)).ToArray(),
                                Events: p.Events.Select(Instantiate).ToArray(), Reads: p.Reads.Select(r => (Value: interpreter.Instantiate(r.Value), r.BeforeEffect)).ToArray())).ToArray();
                            if (uncertain || expected.Any(p => p.Conditions.Any(g => g.Value is null) || p.Events.Any(e => e is null))) { Unmatched(1, "字段、长度或事件纯项没有唯一定义"); continue; }
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
                                if (!matched || candidates is not [var one] || !used.Add(one)) { Unmatched(2, "路径条件没有唯一对应"); matched = false; break; }
                                bool called = false; int beforeEffect = 0;
                                var effects = path.Points.Select(p => blocks[p.Block].Statements[p.Before]).Where(s => s is MemoryWrite or Call).ToArray();
                                foreach (var p in path.Points)
                                {
                                    var statement = blocks[p.Block].Statements[p.Before];
                                    if (statement is MemoryRead read && !AllocationConstructorQuery.PrivateAccess(c, state, locations, read))
                                    {
                                        if (called || c.Get(state.Read, read.Identity) is not { IsSuccess: true } loaded) { matched = false; break; }
                                        var readAddress = c.Get(state.Resolve, read.Address);
                                        var readLocation = readAddress.IsSuccess ? c.Get(state.Locations, new(readAddress.Value, read.Width)) : readAddress.Propagate<Location>();
                                        bool AtPosition(int expectedPosition)
                                        {
                                            if (expectedPosition > effects.Length) return false;
                                            // 读取跨越的每次写入都必须不相交；相同事件位置不需要别名假设。
                                            for (int i = Math.Min(beforeEffect, expectedPosition); i < Math.Max(beforeEffect, expectedPosition); i++)
                                            {
                                                if (effects[i] is not MemoryWrite write) return false;
                                                var writeAddress = c.Get(state.Resolve, write.Address);
                                                var writeLocation = writeAddress.IsSuccess ? c.Get(state.Locations, new(writeAddress.Value, write.Width)) : writeAddress.Propagate<Location>();
                                                if (!readLocation.IsSuccess || !writeLocation.IsSuccess
                                                    || c.Get(state.Alias, new(readLocation.Value, writeLocation.Value)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint }) return false;
                                            }
                                            return true;
                                        }
                                        if (!expected[one].Reads.Any(r => r.Value == loaded.Value && AtPosition(r.BeforeEffect))) { Unmatched(3, "读取值或读取的事件位置不同：" + (read.Trace?.NativeAddress.ToString("x") ?? "无追溯")); matched = false; break; }
                                    }
                                    called |= statement is Call;
                                    if (statement is MemoryWrite or Call) beforeEffect++;
                                }
                                if (!matched) break;
                                var wanted = expected[one].Events; int next = 0;
                                bool Implied(AccessorCheck check, Point at) => c.Get(new PathFactQuery(state), new(at, check.FailureCondition)) is { IsSuccess: true, Value: PathTruth.False };
                                void SkipImplied(Point at)
                                {
                                    while (next < wanted.Length && wanted[next] is AccessorCheck check && Implied(check, at)) next++;
                                }
                                foreach (var id in path.Edges.Select(e => e.Source).Concat(path.ReturnBlock is { } tail ? [tail] : []))
                                {
                                    foreach (var p in path.Points.Where(p => p.Block == id))
                                    {
                                        var statement = blocks[p.Block].Statements[p.Before];
                                        if (statement is MemoryRead) continue;
                                        SkipImplied(p);
                                        if (next >= wanted.Length || !EventEquals(c, statement, p, wanted[next]!)) { Unmatched(4 + next, "事件不相同：" + statement.GetType().Name + " / " + (next < wanted.Length ? wanted[next]!.GetType().Name : "模板已结束")); matched = false; break; }
                                        next++;
                                    }
                                    if (!matched) break;
                                    if (blocks[id].End is not Branch gate) continue;
                                    var edge = path.Edges.Single(e => e.Source == id);
                                    var failureEdge = new FlowEdge(edge.Source, gate.True == edge.Target ? gate.False : gate.True);
                                    SkipImplied(new(edge.Source, blocks[edge.Source].Statements.Length));
                                    var check = regionChecks.SingleOrDefault(check => check.FailureEdge == failureEdge);
                                    if (check is null) continue;
                                    if (check.Kind == "ThrowNullReference" && check.Subject.Value == binding.GetValueOrDefault(-1)) continue;
                                    if (next < wanted.Length && wanted[next] is AccessorCheck expectedCheck && CheckEquals(c, check, expectedCheck)) { next++; continue; }
                                    if (!check.CanAbsorb) { Unmatched(4 + next, "检查种类、被检查值或事件位置不同：" + check.Kind); matched = false; break; }
                                }
                                var last = path.ReturnBlock ?? path.Edges[^1].Source;
                                SkipImplied(new(last, blocks[last].Statements.Length));
                                if (!matched || next != wanted.Length) { if (matched) Unmatched(4 + next, "模板仍有未对应事件或路径事实不足"); matched = false; break; }

                            }
                            if (!matched || used.Count != expected.Length || !window.Any(s => s.Identity == anchor.Identity)) continue;
                            // 所有读取必须是模板纯项；不能留下未解释的堆访问。
                            if (points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<MemoryRead>().Any(r => !reads.Contains(r.Identity)
                                && !AllocationConstructorQuery.PrivateAccess(c, state, locations, r))) { Unmatched(100, "区域含未对应的托管读取"); continue; }
                            if (regionChecks.Where(check => check.CanAbsorb).Any(check => check.Accesses.Any(p => blocks[p.Block].Statements[p.Before] is MemoryRead r && !reads.Contains(r.Identity)))) continue;
                            if (points.Where(p => p.Block == entry.Identity).Any(p => blocks[p.Block].Statements[p.Before] is Call)) continue;
                            var symbolic = Symbols(c.Snapshot.Terms, selected, fixedArgs, binding, template.Anchors, out var free);
                            var constraint = new AccessorTerms(c.Snapshot.Terms, i => symbolic.GetValueOrDefault(i), Read, arrayLength: Length);
                            IEnumerable<Term> Inputs(AccessorEvent effect) => effect switch
                            {
                                AccessorFieldWrite w => [w.Receiver, w.Value],
                                AccessorArrayWrite w => [w.Array, w.Index, w.Value],
                                AccessorCheck check => check.Inputs.Select(i => i.Value).Append(check.FailureCondition),
                                AccessorInvocation call => call.Arguments.Concat(call.Receiver is { } receiver ? [receiver] : []), _ => [],
                            };
                            var equations = template.Paths.SelectMany(p => p.Conditions.Select(g => g.Value).Concat(p.Events.SelectMany(Inputs)))
                                .Select(constraint.Instantiate).OfType<Term>().ToArray();
                            Reason? placement = free.All(p => equations.Any(e => Determines(e, p))) ? Available(c, point, binding.Values.Concat(returned), sites)
                                : new("inline.Accessor.Ambiguous", "带事件条件模板的形参没有完整可逆约束");
                            var outside = blocks.Values.SelectMany(b => b.Statements.Select((s, i) => (s, p: new Point(b.Identity, i)))
                                .Where(x => !points.Contains(x.p)).SelectMany(x => SnapshotRewrite.Uses(x.s))
                                .Concat(area.Value.Order.Append(entry.Identity).Contains(b.Identity) ? [] : SnapshotRewrite.Uses(b.End))).Concat(returned);
                            var coveredValues = points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<MemoryRead>().Where(r => reads.Contains(r.Identity))
                                .Select(r => c.Get(state.Read, r.Identity)).Where(v => v.IsSuccess).Select(v => v.Value).ToHashSet();
                            var removedDefinitions = points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<Call>().Select(call => (StableIdentity)call.Identity)
                                .Concat(area.Value.Order.SelectMany(id => blocks[id].Merges.Select(merge => merge.Identity))).ToHashSet();
                            var seen = new HashSet<Term>();
                            bool Escapes(Term term)
                            {
                                if (!seen.Add(term)) return false;
                                // 循环下一轮的读取有自己的定义；不能把它的内存合流误作本轮旧值的使用。
                                if (term.Identity is ResultAtom { Definition: ReadIdentity read }) return reads.Contains(read);
                                if (term.Identity is ResultAtom atom && removedDefinitions.Contains(atom.Definition))
                                {
                                    var resolved = c.Get(state.Resolve, term);
                                    return !resolved.IsSuccess || resolved.Value == term || Escapes(resolved.Value);
                                }
                                if (term.Identity is ResultAtom { Definition: MergeIdentity id })
                                {
                                    var owner = blocks.Values.Single(b => b.Merges.Any(m => m.Identity == id));
                                    var merge = owner.Merges.Single(m => m.Identity == id);
                                    if (owner.Identity == join)
                                    {
                                        var folded = merge.Inputs.Where(i => i.Predecessor == entry.Identity || area.Value.Order.Contains(i.Predecessor))
                                            .Select(i => c.Get(state.Resolve, i.Value)).ToArray();
                                        if (folded.Length == 0 || folded.Any(v => !v.IsSuccess) || folded.Select(v => v.Value).Distinct().Count() != 1
                                            || Available(c, point, [folded[0].Value], sites) is not null) return true;
                                    }
                                    return merge.Inputs.Any(i => Escapes(i.Value));
                                }
                                if (coveredValues.Contains(term) || term.Identity is MemoryMerge memory && area.Value.Order.Contains(memory.Block)) return true;
                                return term.Operands.Any(Escapes);
                            }
                            if (outside.Any(Escapes)) placement = new("inline.Accessor.Placement", "区域内读到的字段值在区域外另有使用");
                            var replacement = new AccessorReplacement(selected, selected.Method.IsStatic ? null : binding[-1],
                                Enumerable.Range(0, selected.Method.Parameters.Count).Select(i => binding[i]).ToArray(), null, point, reads.ToArray(),
                                points.Select(p => blocks[p.Block].Statements[p.Before]).OfType<MemoryWrite>().Select(w => w.Identity).ToArray())
                                { Region = new(entry.Identity, join, area.Value.Order) { Return = returnEnd } };
                            var coverage = SnapshotRewrite.Dependencies(roots.Select(r => c.Get(state.Resolve, r)).Where(v => v.IsSuccess).Select(v => v.Value));
                            if (!matches.Any(m => m.Replacement.Method.Equals(selected) && m.Replacement.Point == point && m.Replacement.Region?.Join == join
                                && m.Replacement.Arguments.SequenceEqual(replacement.Arguments) && m.Replacement.Receiver == replacement.Receiver))
                                matches.Add(new(replacement, coverage, placement));
                        }
                    }
                }
            }
            if (matches.Count == 0) shapes.Add("带事件条件模板未匹配：" + (detail ?? "没有从锚点字段的读取通向公共续点的区域"));
        }
        private bool CheckEquals(QueryContext c, ConditionalCheck actual, AccessorCheck expected)
        {
            if (actual.Kind != expected.Kind) return false;
            var inputs = new[] { ("value", actual.Subject.Value), ("index", actual.Subject.Index), ("length", actual.Subject.Length), ("array", actual.Subject.Array) }
                .Where(i => i.Item2 is not null).Select(i => new AccessorCheckInput(i.Item1, i.Item2!)).ToArray();
            if (inputs.Length == 0) return false;
            return inputs.Length == expected.Inputs.Count && inputs.Zip(expected.Inputs).All(pair => pair.First.Role == pair.Second.Role
                && c.Get(state.Resolve, pair.First.Value) is { IsSuccess: true } value && value.Value == pair.Second.Value);
        }
        private bool EventEquals(QueryContext c, Statement actual, Point point, AccessorEvent expected)
        {
            Term? Resolve(Term term) => c.Get(state.Resolve, term) is { IsSuccess: true } value ? value.Value : null;
            if (actual is MemoryWrite { Release: false } write && Resolve(write.Value) is { } value
                && c.Get(locations, new(write.Address, write.Width)) is { IsSuccess: true } at)
            {
                var views = at.Value.Views.Where(v => v.Offset == 0 && types.Size(v.Type) * 8 == write.Width).ToArray();
                if (views is not [var view]) return false;
                if (expected is AccessorArrayWrite element) return view.Kind == ManagedLocationKind.ArrayElement && view.Path.IsEmpty
                    && Resolve(view.Root) == element.Array && view.Index is { } index && Resolve(index) == element.Index && value == element.Value;
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
