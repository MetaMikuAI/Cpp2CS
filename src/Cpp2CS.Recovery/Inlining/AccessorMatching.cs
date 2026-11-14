using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Inlining;

public sealed record AccessorReplacement(MethodRef Method, Term? Receiver, IReadOnlyList<Term> Arguments,
    Term? Result, Point Point, IReadOnlyList<ReadIdentity> Reads, IReadOnlyList<WriteIdentity> Writes)
{
    public bool Negated { get; init; }
    public CallIdentity? Call { get; init; }
    public AccessorRegion? Region { get; init; }
    public IEnumerable<StableIdentity> Accesses => Reads.Cast<StableIdentity>().Concat(Writes).Concat(Call is { } call ? [call] : []).Concat(Region is { } region ? region.Blocks.Append(region.Entry) : []);
}
public sealed record AccessorRegion(BlockIdentity Entry, BlockIdentity Join, IReadOnlyList<BlockIdentity> Blocks);
public sealed record AccessorCallSite(MethodRef Method, BoundCall Binding, bool Virtual, Term? Receiver);
public sealed record AccessorProgram(IReadOnlyList<AccessorReplacement> Replacements,
    IReadOnlyDictionary<StableIdentity, Reason> Failures);

public sealed partial class AccessorQuery
{
    public Outcome<AccessorProgram> Match(QueryContext context, MethodRef caller, StateQueries state,
        ManagedLocationQuery locations, IReadOnlyDictionary<Term, ManagedValue> arguments,
        IReadOnlyDictionary<CallIdentity, AccessorCallSite>? calls = null) =>
        context.Get(new ProgramQuery(types, templates, state, locations, caller, arguments, calls, observe, Find), 0);

    private sealed record Site(Point Point, StableIdentity Identity, FieldRef Field, Term? Receiver, TypeRef? ReceiverType,
        Term Value, bool Write, ulong Address);
    private sealed record TemplateParameter(MethodDef Method, int Index) : AtomIdentity
    { public override string StableText => "inline.accessor-parameter"; }
    private sealed record CandidateMatch(AccessorReplacement Replacement, HashSet<Term> Coverage, Reason? Placement)
    { public HashSet<StableIdentity> Accesses { get; } = [.. Replacement.Accesses]; }

    /// <summary>发现纯项、转调和无副作用区域；读取版本、支配、路径事实与最终相等均取现有查询。</summary>
    private sealed partial class ProgramQuery(ManagedTypes types, IAccessorTemplateSource templates, StateQueries state,
        ManagedLocationQuery locations, MethodRef caller, IReadOnlyDictionary<Term, ManagedValue> arguments,
        IReadOnlyDictionary<CallIdentity, AccessorCallSite>? calls, Action<AccessorAttempt>? observe, Func<AccessorAccess, AccessorAnswer> Legacy) : Query<int, AccessorProgram>
    {
        private readonly FlowQueries flow = new();
        public override Outcome<AccessorProgram> Compute(QueryContext c, int key)
        {
            var sites = new List<Site>(); var failures = new Dictionary<StableIdentity, Reason>();
            var replacements = new List<AccessorReplacement>();
            var blocks = c.Snapshot.Blocks.ToDictionary(b => b.Identity);
            var allTerms = new HashSet<Term>();
            foreach (var block in c.Snapshot.Blocks)
            {
                for (int i = 0; i < block.Statements.Length; i++)
                {
                    var statement = block.Statements[i];
                    var (address, width) = statement switch { MemoryRead r => (r.Address, r.Width), MemoryWrite w => (w.Address, w.Width), _ => ((Term?)null, 0) };
                    if (address is null) continue;
                    var located = c.Get(locations, new(address, width));
                    if (!located.IsSuccess) continue;
                    var views = located.Value.Views.Where(v => v.Offset == 0 && v.Path.Length == 1
                        && types.Size(v.Type) * 8 == width && v.Kind is ManagedLocationKind.InstanceField or ManagedLocationKind.StaticField).ToArray();
                    if (views is not [var view]) continue;
                    var field = view.Path[0]; Term? receiver = null; TypeRef? receiverType = null;
                    if (!field.Field.IsStatic)
                    {
                        var root = c.Get(state.Resolve, view.Root); if (!root.IsSuccess) continue;
                        receiver = root.Value;
                        var typed = c.Get(locations.Types, view.Root);
                        receiverType = typed.IsSuccess ? typed.Value?.Type : null;
                        receiverType ??= types.Kind(field.DeclaringType) == TypeKind.Struct ? new ByRefRef(field.DeclaringType) : field.DeclaringType;
                    }
                    var value = statement is MemoryRead read ? c.Get(state.Read, read.Identity) : c.Get(state.Resolve, ((MemoryWrite)statement).Value);
                    if (!value.IsSuccess || statement is MemoryRead && value.Value.Identity is not (MemoryAtom or MemoryMerge)) continue;
                    var identity = statement is MemoryRead rr ? (StableIdentity)rr.Identity : ((MemoryWrite)statement).Identity;
                    sites.Add(new(new(block.Identity, i), identity, field, receiver, receiverType, value.Value, statement is MemoryWrite, statement.Trace?.NativeAddress ?? 0));
                    if (statement is MemoryRead) allTerms.Add(value.Value);
                }
            }
            var anchors = sites.Where(s => !ManagedAccess.Field(types, caller, s.Field, s.ReceiverType)).ToArray();
            if (anchors.Length == 0) return Outcome<AccessorProgram>.Success(new([], failures));
            foreach (var block in c.Snapshot.Blocks)
                foreach (var root in block.Statements.SelectMany(SnapshotRewrite.Uses).Concat(SnapshotRewrite.Uses(block.End)))
                {
                    var resolved = c.Get(state.Resolve, root);
                    if (resolved.IsSuccess) allTerms.UnionWith(SnapshotRewrite.Dependencies([resolved.Value]));
                }
            var consumed = new HashSet<StableIdentity>();
            foreach (var anchor in anchors.OrderByDescending(s => s.Write))
            {
                if (consumed.Contains(anchor.Identity)) continue;
                var matches = new List<CandidateMatch>(); var incomplete = new List<AccessorCandidateFailure>();
                var shapes = new HashSet<string>(); int candidates = 0;
                var block = blocks[anchor.Point.Block];
                // 事件与写入截断取值范围；赋值组另按全部连续字段写入复核。
                int low = anchor.Point.Before, high = low + 1;
                while (low > 0 && Quiet(c, block.Statements[low - 1], !anchor.Write)) low--;
                while (high < block.Statements.Length && Quiet(c, block.Statements[high], !anchor.Write)) high++;
                int readLow = low;
                if (anchor.Write)
                    while (readLow > 0 && Quiet(c, block.Statements[readLow - 1], true)) readLow--;
                var window = sites.Where(s => s.Point.Block == anchor.Point.Block && s.Point.Before >= readLow && s.Point.Before < high).ToArray();
                var writesInWindow = window.Where(s => s.Write && s.Point.Before >= low && s.Receiver == anchor.Receiver).ToArray();
                foreach (var candidate in anchor.Field.Field.Owner.Methods.Where(m => m.Name is not (".ctor" or ".cctor")
                    && !m.IsOverridable
                    && m.GenericParameters.Count == 0 && (!anchor.Write || ManagedTypes.IsVoid(m.ReturnType))))
                {
                    if (c.Step() is { } budget) return Outcome<AccessorProgram>.Failure(budget);
                    if (anchor.Field.DeclaringType is not DefinitionRef instance) continue;
                    var selected = new MethodRef(candidate, instance.Arguments, []);
                    if (!ManagedAccess.Method(types, caller.Method.Owner, selected, candidate.IsStatic ? null : anchor.ReceiverType)) continue;
                    candidates++;
                    if (types.Kind(selected.Concrete(candidate.ReturnType)) == TypeKind.Struct
                        || candidate.Parameters.Any(p => types.Kind(selected.Concrete(p.Type)) == TypeKind.Struct))
                    { shapes.Add("候选的方法体不是模板：CompositeSignature；复合参数或返回值需要整体模板"); continue; }
                    var result = templates.Get(candidate);
                    if (result.Status == AccessorTemplateStatus.Incomplete) { incomplete.Add(new(candidate, result.Failure)); continue; }
                    if (result.Template is not { } template) { if (result.Failure is { } why) shapes.Add(why.Message); continue; }
                    if (template.Kind != (anchor.Write ? AccessorKind.Setter : AccessorKind.Getter)) continue;
                    var templateFields = template.Fields.Select(f => f with { DeclaringType = selected.Concrete(f.DeclaringType) }).ToHashSet();
                    var group = writesInWindow.Where(s => templateFields.Contains(s.Field)).ToArray();
                    var values = template.Conditional is { } conditional ? conditional.Anchors.ToArray()
                        : template.Call is { } invocation ? invocation.Arguments.Concat(invocation.Receiver is { } self ? [self] : []).ToArray()
                        : template.Expression is { } expression ? new[] { expression }
                        : template.Stores.SelectMany(s => new[] { s.Target, s.Value }).ToArray();
                    var fieldNodes = values.SelectMany(ManagedValues.Walk).Where(v => FieldAccessor.FieldOf(v)?.Field == anchor.Field.Field).Distinct().ToArray();
                    foreach (var fieldNode in fieldNodes)
                    {
                        var fixedArgs = new Dictionary<int, Term>();
                        if (fieldNode is FieldValue { Receiver: ArgumentValue p })
                        { if (anchor.Receiver is null) continue; fixedArgs[p.Index] = anchor.Receiver; }
                        else if (fieldNode is not StaticFieldValue) continue;
                        if (!candidate.IsStatic && !fixedArgs.ContainsKey(-1)) continue;
                        if (template.Conditional is { } paths)
                        {
                            Conditional(c, anchor, selected, paths, fixedArgs, window, sites, allTerms, blocks, matches, shapes);
                            if (c.Step() is { } exhausted) return Outcome<AccessorProgram>.Failure(exhausted);
                            continue;
                        }
                        if (template.Call is { } forwarded)
                        {
                            if (high < block.Statements.Length && block.Statements[high] is Call call && calls?.GetValueOrDefault(call.Identity) is { } actual)
                                Forward(c, anchor, selected, forwarded, actual, call, new(block.Identity, high), block, fixedArgs, window, sites, values, matches, shapes);
                            else shapes.Add("转调未匹配：字段读取之后没有可配对的已绑定调用；被调访问器再次展开时需两层证明");
                            if (c.Step() is { } exhausted) return Outcome<AccessorProgram>.Failure(exhausted);
                            continue;
                        }
                        Term?[] roots;
                        if (anchor.Write) roots = [null];
                        else if (Enumerable.Range(0, candidate.Parameters.Count).All(fixedArgs.ContainsKey))
                        {
                            var fixedInterpreter = new AccessorTerms(c.Snapshot.Terms, index => fixedArgs.GetValueOrDefault(index), (field, receiver) =>
                            {
                                var found = ReadSites(window, selected, field, receiver).Select(s => s.Value).Distinct().ToArray();
                                return found is [var one] ? one : null;
                            });
                            var fixedTerm = fixedInterpreter.Read(template.Expression!);
                            if (fixedTerm is not null) fixedTerm = fixedInterpreter.Result(fixedTerm);
                            roots = fixedTerm is null ? [] : new[] { fixedTerm, fixedTerm.Width == 1
                                ? c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, fixedTerm) : fixedTerm }
                                .Distinct().Where(allTerms.Contains).Cast<Term?>().ToArray();
                        }
                        else roots = allTerms.Where(t => t.Width <= 64 && !t.ContainsUndefined).Cast<Term?>().ToArray();
                        foreach (var target in roots)
                        {
                            var possible = target is null ? SnapshotRewrite.Dependencies(group.Select(s => s.Value)) : SnapshotRewrite.Dependencies([target]);
                            possible.UnionWith(arguments.Keys);
                            // 绑定只是发现；每一种完整代入仍须由最终项相等复核。
                            foreach (var binding in Bindings(c.Snapshot.Terms, selected, possible, fixedArgs))
                            {
                                if (c.Step() is { } why) return Outcome<AccessorProgram>.Failure(why);
                                var reads = new List<Site>(); bool uncertain = false;
                                var interpreter = new AccessorTerms(c.Snapshot.Terms, index => binding.GetValueOrDefault(index), (field, receiver) =>
                                {
                                    var found = ReadSites(window, selected, field, receiver);
                                    if (found.Length == 0 || found.Select(s => s.Value).Distinct().Count() != 1) { uncertain = true; return null; }
                                    reads.AddRange(found); return found[0].Value;
                                });
                                var writes = new List<Site>(); bool negated = false;
                                if (target is not null)
                                {
                                    var expected = interpreter.Read(template.Expression!);
                                    if (expected is not null) expected = interpreter.Result(expected);
                                    negated = expected is { Width: 1 } && c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, expected) == target;
                                    if (expected != target && !negated || uncertain || !reads.Any(s => s.Identity == anchor.Identity)
                                        || !SnapshotRewrite.Dependencies([target]).Overlaps(reads.Select(s => s.Value))) continue;
                                }
                                else
                                {
                                    if (group.Length != template.Stores.Count || group.Select(s => s.Field).Distinct().Count() != group.Length) continue;
                                    foreach (var store in template.Stores)
                                    {
                                        var field = FieldAccessor.FieldOf(store.Target)!;
                                        field = field with { DeclaringType = selected.Concrete(field.DeclaringType) };
                                        var actual = group.Where(s => s.Field.Equals(field)).ToArray();
                                        if (actual is not [var one]) { uncertain = true; break; }
                                        Term? receiver = store.Target is FieldValue f ? interpreter.Read(f.Receiver) : null;
                                        var expected = interpreter.Read(store.Value);
                                        if (receiver != one.Receiver || expected is null || interpreter.Resize(expected, one.Value.Width) != one.Value)
                                        { uncertain = true; break; }
                                        writes.Add(one);
                                    }
                                    if (uncertain || writes.Count != group.Length || !writes.Any(s => s.Identity == anchor.Identity)) continue;
                                }
                                reads = reads.DistinctBy(s => s.Identity).ToList();
                                var included = reads.Concat(writes).ToArray();
                                var point = (writes.Count != 0 ? writes : included.AsEnumerable()).MinBy(s => s.Point.Before)!.Point;
                                var symbolic = Symbols(c.Snapshot.Terms, selected, fixedArgs, binding, values, out var free);
                                var constraintReader = new AccessorTerms(c.Snapshot.Terms, index => symbolic.GetValueOrDefault(index), (field, receiver) =>
                                {
                                    var found = ReadSites(window, selected, field, receiver).Select(s => s.Value).Distinct().ToArray();
                                    return found is [var one] ? one : null;
                                });
                                var equations = target is not null ? new[] { constraintReader.Read(template.Expression!) }
                                    : template.Stores.Select(s => constraintReader.Read(s.Value) is { } value
                                        ? constraintReader.Resize(value, types.StorageBits(selected.Concrete(s.Target.Type))) : null).ToArray();
                                bool unique = free.All(parameter => equations.OfType<Term>().Any(e => Determines(e, parameter)));
                                Reason? placement = unique ? Placement(c, block, included, point, binding, reads, target, sites)
                                    : new("inline.Accessor.Ambiguous", "形参的完整值没有可逆约束，存在未区分的实参代入");
                                var replacement = new AccessorReplacement(selected, candidate.IsStatic ? null : binding[-1],
                                    Enumerable.Range(0, candidate.Parameters.Count).Select(i => binding[i]).ToArray(), target, point,
                                    reads.Select(s => (ReadIdentity)s.Identity).ToArray(), writes.Select(s => (WriteIdentity)s.Identity).ToArray()) { Negated = negated };
                                var coverage = target is null ? new HashSet<Term>(writes.Select(s => s.Value)) : SnapshotRewrite.Dependencies([target]);
                                coverage.UnionWith(reads.Select(s => s.Value));
                                if (!matches.Any(m => m.Replacement.Method.Equals(selected) && m.Replacement.Result == target
                                    && m.Replacement.Arguments.SequenceEqual(replacement.Arguments) && m.Replacement.Receiver == replacement.Receiver))
                                    matches.Add(new(replacement, coverage, placement));
                            }
                        }
                    }
                }
                // 覆盖按项的包含关系取极大值；不可比较的解释也保留歧义。
                var best = matches.Where(m => !matches.Any(other => other.Coverage.IsSupersetOf(m.Coverage) && other.Accesses.IsSupersetOf(m.Accesses)
                    && (other.Coverage.IsProperSupersetOf(m.Coverage) || other.Accesses.IsProperSupersetOf(m.Accesses)))).ToArray();
                Reason? failure = best.Length > 1 ? new("inline.Accessor.Ambiguous", $"有 {best.Length} 个最大覆盖或不同实参代入，无法区分原调用")
                    : best.Length == 1 ? best[0].Placement
                    : new("inline.Accessor.None", candidates == 0 ? "没有候选" : incomplete.Count == candidates ? "候选未能完整恢复"
                        : shapes.Count != 0 ? string.Join("；", shapes.Order(StringComparer.Ordinal)) : "候选模板与完整项或写入组不匹配",
                        new("inline.anchor", (anchor.Write ? "写入 " : "读取 ") + anchor.Field.Field.Owner.FullName + "." + anchor.Field.Field.Name));
                var access = new AccessorAccess(caller, anchor.Address, anchor.Field, anchor.ReceiverType,
                    anchor.Write ? AccessorKind.Setter : AccessorKind.Getter, failure is null);
                if (best.Length == 1 && failure is null)
                {
                    var accepted = best[0].Replacement;
                    // 同一读取不能被两个不同调用消费。
                    if (accepted.Accesses.Any(consumed.Contains))
                        failure = new("inline.Accessor.Ambiguous", "不同内联解释消费了同一次字段访问");
                    else
                    {
                        replacements.Add(accepted); consumed.UnionWith(accepted.Accesses);
                        observe?.Invoke(new(access, new(accepted.Method, null, Matches: 1) { IncompleteCandidates = incomplete }));
                        continue;
                    }
                }
                // 既有单字段证明仍可处理复合接收者；它不替代更大的已匹配表达式或歧义。
                bool singlePlacement = best is [var single] && single.Replacement.Result == anchor.Value
                    && templates.Get(single.Replacement.Method.Method).Template?.SingleField == true;
                if (failure?.Code != "inline.Accessor.Ambiguous" && (best.Length == 0 || singlePlacement)
                    && Legacy(access with { HasPlacement = true }).Method is not null) continue;
                failures[anchor.Identity] = failure!;
                // 失败在实际使用处报告，未使用的读取不额外制造洞。
            }
            return Outcome<AccessorProgram>.Success(new(replacements, failures));
        }

        private static Site[] ReadSites(IEnumerable<Site> window, MethodRef selected, FieldRef field, Term? receiver)
        {
            var concrete = field with { DeclaringType = selected.Concrete(field.DeclaringType) };
            return window.Where(s => !s.Write && s.Field.Equals(concrete) && s.Receiver == receiver).ToArray();
        }

        private Dictionary<int, Term> Symbols(TermTable terms, MethodRef selected, Dictionary<int, Term> fixedArgs,
            Dictionary<int, Term> binding, IEnumerable<ManagedValue> values, out List<Term> free)
        {
            var symbolic = new Dictionary<int, Term>(fixedArgs); free = [];
            var roots = values.SelectMany(ManagedValues.Walk).OfType<FieldValue>()
                .Select(f => f.Receiver).OfType<ArgumentValue>().Select(a => a.Index).ToHashSet();
            foreach (int index in Enumerable.Range(0, selected.Method.Parameters.Count).Where(i => !fixedArgs.ContainsKey(i)))
            {
                // 字段位置精确绑定其对象；其余形参必须保留完整值的可逆约束。
                if (roots.Contains(index)) { symbolic[index] = binding[index]; continue; }
                var type = selected.Concrete(selected.Method.Parameters[index].Type); int width = types.StorageBits(type);
                // C++ bool 只有两值，解释与现场写入仍按声明存储位宽复核。
                var parameter = terms.Atom(new TemplateParameter(selected.Method, index), types.Kind(type) == TypeKind.Bool ? 1 : width);
                free.Add(parameter); symbolic[index] = parameter.Width == width ? parameter
                    : terms.Apply(new CoreOperator(CoreOperation.ZeroExtend), width, parameter);
            }
            return symbolic;
        }

        private IEnumerable<Dictionary<int, Term>> Bindings(TermTable terms, MethodRef selected, HashSet<Term> possible,
            Dictionary<int, Term> fixedArgs, int index = 0)
        {
            if (index == selected.Method.Parameters.Count) { yield return fixedArgs; yield break; }
            if (fixedArgs.ContainsKey(index))
            { foreach (var b in Bindings(terms, selected, possible, fixedArgs, index + 1)) yield return b; yield break; }
            int width = types.StorageBits(selected.Concrete(selected.Method.Parameters[index].Type));
            if (width is <= 0 or > 64) yield break;
            var inputs = possible.Where(t => t.Width == width);
            if (types.Kind(selected.Concrete(selected.Method.Parameters[index].Type)) == TypeKind.Bool)
            {
                var interpreter = new AccessorTerms(terms, _ => null, (_, _) => null);
                inputs = inputs.Select(t => interpreter.Resize(terms.Slice(t, 0, 1), width))
                    .Concat(possible.Where(t => t.Width == 1).Select(t => interpreter.Resize(t, width)))
                    .Concat(new[] { terms.Constant(0, width), terms.Constant(1, width) });
            }
            foreach (var term in inputs.Distinct().Where(t => !t.ContainsUndefined
                && t.Kind is not (TermKind.Unknown or TermKind.Undefined)))
            {
                var next = new Dictionary<int, Term>(fixedArgs) { [index] = term };
                foreach (var b in Bindings(terms, selected, possible, next, index + 1)) yield return b;
            }
        }

        private void Forward(QueryContext c, Site anchor, MethodRef selected, ManagedInvocation forwarded,
            AccessorCallSite actual, Call call, Point point, Block block, Dictionary<int, Term> fixedArgs,
            Site[] window, List<Site> sites, ManagedValue[] values, List<CandidateMatch> matches, HashSet<string> shapes)
        {
            var target = new MethodRef(forwarded.Method.Method, forwarded.Method.TypeArguments.Select(selected.Concrete).ToArray(),
                forwarded.Method.MethodArguments.Select(selected.Concrete).ToArray());
            if (!actual.Method.Equals(target) || actual.Virtual != forwarded.Virtual)
            { shapes.Add("转调未匹配：被调方法或分派身份不同"); return; }
            var sources = new BoundSourceQuery(state);
            Term? Input(BoundValue? value)
            {
                if (value?.Source is null) return null;
                var input = c.Get(sources, new(value.Source, point));
                if (!input.IsSuccess) return null;
                var resolved = c.Get(state.Resolve, input.Value);
                return resolved.IsSuccess ? resolved.Value : null;
            }
            var receiver = actual.Receiver is { } self ? c.Get(state.Resolve, self) : default;
            var actualSelf = actual.Receiver is not null ? receiver.IsSuccess ? receiver.Value : null : Input(actual.Binding.This);
            if (forwarded.Virtual && (forwarded.Receiver is null || actualSelf is null
                || c.Get(locations.Types, actualSelf) is not { IsSuccess: true, Value.Type: { } staticType }
                || !staticType.Equals(selected.Concrete(forwarded.Receiver.Type)) || actual.Method.Method.Slot != target.Method.Slot))
            { shapes.Add("转调未匹配：虚槽或接收者静态类型不同"); return; }
            var actualArgs = actual.Binding.Parameters.Select(p => Input(p)).ToArray();
            if (actualArgs.Length != forwarded.Arguments.Count || actualArgs.Any(t => t is null)
                || (forwarded.Receiver is null) != (actualSelf is null))
            { shapes.Add("转调未匹配：ABI 输入不完整"); return; }
            var actualInputs = actualArgs.OfType<Term>().Concat(actualSelf is null ? [] : new[] { actualSelf }).ToArray();
            var possible = SnapshotRewrite.Dependencies(actualInputs); possible.UnionWith(arguments.Keys);
            var result = ManagedTypes.IsVoid(selected.Method.ReturnType) ? null : Input(actual.Binding.Result);
            if (!ManagedTypes.IsVoid(selected.Method.ReturnType) && result is null)
            { shapes.Add("转调未匹配：调用结果没有完整标量绑定"); return; }
            foreach (var binding in Bindings(c.Snapshot.Terms, selected, possible, fixedArgs))
            {
                if (c.Step() is not null) return;
                var reads = new List<Site>(); bool uncertain = false;
                Term? Read(FieldRef field, Term? owner)
                {
                    var found = ReadSites(window, selected, field, owner);
                    if (found.Length == 0 || found.Select(s => s.Value).Distinct().Count() != 1) { uncertain = true; return null; }
                    reads.AddRange(found); return found[0].Value;
                }
                var interpreter = new AccessorTerms(c.Snapshot.Terms, i => binding.GetValueOrDefault(i), Read);
                if (forwarded.Receiver is { } expectedSelf && interpreter.Read(expectedSelf) != actualSelf) continue;
                if (forwarded.Arguments.Select(interpreter.Read).Where((term, i) => term != actualArgs[i]).Any()
                    || uncertain || !reads.Any(s => s.Identity == anchor.Identity)) continue;
                reads = reads.DistinctBy(s => s.Identity).ToList();
                var symbolic = Symbols(c.Snapshot.Terms, selected, fixedArgs, binding, values, out var free);
                var constraint = new AccessorTerms(c.Snapshot.Terms, i => symbolic.GetValueOrDefault(i), Read);
                var equations = values.Select(constraint.Read).OfType<Term>().ToArray();
                reads = reads.DistinctBy(s => s.Identity).ToList();
                var placement = free.All(p => equations.Any(e => Determines(e, p)))
                    ? Placement(c, block, reads.ToArray(), point, binding, reads, result, sites, call.Identity)
                    : new Reason("inline.Accessor.Ambiguous", "转调形参的完整值没有可逆约束");
                var replacement = new AccessorReplacement(selected, selected.Method.IsStatic ? null : binding[-1],
                    Enumerable.Range(0, selected.Method.Parameters.Count).Select(i => binding[i]).ToArray(), result, point,
                    reads.Select(s => (ReadIdentity)s.Identity).ToArray(), []) { Call = call.Identity };
                var coverage = SnapshotRewrite.Dependencies(actualInputs); if (result is not null) coverage.Add(result);
                if (!matches.Any(m => m.Replacement.Method.Equals(selected) && m.Replacement.Call == call.Identity
                    && m.Replacement.Arguments.SequenceEqual(replacement.Arguments) && m.Replacement.Receiver == replacement.Receiver))
                    matches.Add(new(replacement, coverage, placement));
            }
        }

        private static bool Determines(Term value, Term parameter)
        {
            if (value == parameter) return true;
            if (value.Kind == TermKind.Concat) return value.Operands.Any(v => Determines(v, parameter));
            if (value.Operator is not CoreOperator op) return false;
            if (op.Operation is CoreOperation.Not or CoreOperation.Negate or CoreOperation.SignExtend or CoreOperation.ZeroExtend)
                return Determines(value.Operands[0], parameter);
            if (op.Operation is CoreOperation.Add or CoreOperation.Subtract or CoreOperation.Xor)
                return Enumerable.Range(0, value.Operands.Length).Any(i => Determines(value.Operands[i], parameter)
                    && value.Operands.Where((_, j) => j != i).All(v => !SnapshotRewrite.Dependencies([v]).Contains(parameter)));
            if (op.Operation == CoreOperation.Multiply)
                return Enumerable.Range(0, 2).Any(i => value.Operands[1 - i].ConstantValue is { IsEven: false }
                    && Determines(value.Operands[i], parameter));
            return false;
        }

        private bool Quiet(QueryContext c, Statement statement, bool reading)
        {
            if (statement is MemoryRead read)
            {
                if (reading) return true;
                var at = c.Get(state.Locations, new(read.Address, read.Width));
                return at.IsSuccess && at.Value.Region == Region.Frame;
            }
            if (statement is MemoryWrite write)
            {
                if (!reading) return true;
                var at = c.Get(state.Locations, new(write.Address, write.Width));
                return at.IsSuccess && at.Value.Region == Region.Frame;
            }
            return false;
        }
        private Reason? Available(QueryContext c, Point point, IEnumerable<Term> inputs, List<Site> sites)
        {
            Reason No(string message) => new("inline.Accessor.Placement", message);
            foreach (var term in inputs)
                foreach (var dependency in SnapshotRewrite.Dependencies([term]))
                {
                    if (dependency.Kind is TermKind.Unknown or TermKind.Undefined) return No("实参含未知或未定义值");
                    var definitions = sites.Where(s => !s.Write && s.Value == dependency).ToArray();
                    if (definitions.Length != 0 && !definitions.Any(definition => definition.Point with { Before = definition.Point.Before + 1 } == point
                        || c.Get(flow.PointDominates, new(definition.Point with { Before = definition.Point.Before + 1 }, point)) is { IsSuccess: true, Value: true }))
                        return No("实参读取未在调用位置之前定义");
                    if (dependency.Identity is ResultAtom { Definition: CallIdentity callId })
                    {
                        var defined = c.Snapshot.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Point: new Point(b.Identity, i + 1))))
                            .Single(p => p.Statement is Call call && call.Identity == callId).Point;
                        if (defined != point && c.Get(flow.PointDominates, new(defined, point)) is not { IsSuccess: true, Value: true })
                            return No("实参的调用结果不支配调用位置");
                    }
                    BlockIdentity? mergeBlock = dependency.Identity switch
                    {
                        ResultAtom { Definition: MergeIdentity mergeId } => c.Snapshot.Blocks.Single(b => b.Merges.Any(m => m.Identity == mergeId)).Identity,
                        MemoryMerge memory => memory.Block,
                        _ => null,
                    };
                    if (mergeBlock is not null && new Point(mergeBlock, 0) != point
                        && c.Get(flow.PointDominates, new(new Point(mergeBlock, 0), point)) is not { IsSuccess: true, Value: true })
                        return No("实参的合流定义不支配调用位置");
                }
            return null;
        }
        private Reason? Placement(QueryContext c, Block block, Site[] included, Point point, Dictionary<int, Term> binding,
            List<Site> reads, Term? target, List<Site> sites, CallIdentity? consumedCall = null)
        {
            Reason No(string message) => new("inline.Accessor.Placement", message);
            int end = included.Max(s => s.Point.Before);
            int begin = included.Min(s => s.Point.Before);
            var written = included.Where(s => s.Write).ToArray();
            for (int i = 0; i < written.Length; i++)
                for (int j = 0; j < i; j++)
                {
                    var a = (MemoryWrite)block.Statements[written[i].Point.Before];
                    var b = (MemoryWrite)block.Statements[written[j].Point.Before];
                    var left = c.Get(state.Locations, new(a.Address, a.Width));
                    var right = c.Get(state.Locations, new(b.Address, b.Width));
                    if (!left.IsSuccess || !right.IsSuccess || c.Get(state.Alias, new(left.Value, right.Value)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint })
                        return No("字段写入未证明互不重叠");
                }
            foreach (var read in reads)
                foreach (var write in written.Where(w => !w.Field.Equals(read.Field)))
                {
                    var r = (MemoryRead)block.Statements[read.Point.Before];
                    var w = (MemoryWrite)block.Statements[write.Point.Before];
                    var left = c.Get(state.Locations, new(r.Address, r.Width));
                    var right = c.Get(state.Locations, new(w.Address, w.Width));
                    if (!left.IsSuccess || !right.IsSuccess || c.Get(state.Alias, new(left.Value, right.Value)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint })
                        return No("模板读取与其他字段写入未证明互不重叠");
                }
            var ids = included.Select(s => s.Identity).ToHashSet();
            for (int i = begin; i <= end; i++)
            {
                var statement = block.Statements[i];
                if (statement is MemoryRead r && ids.Contains(r.Identity) || statement is MemoryWrite w && ids.Contains(w.Identity)) continue;
                Outcome<Location>? privateLocation = statement switch { MemoryRead readAt => c.Get(state.Locations, new(readAt.Address, readAt.Width)), MemoryWrite writeAt => c.Get(state.Locations, new(writeAt.Address, writeAt.Width)), _ => null };
                if (privateLocation is not { } privateAccess || !privateAccess.IsSuccess || privateAccess.Value.Region != Region.Frame) return No("字段访问之间含未消费的读取、写入或事件");
            }
            if (Available(c, point, binding.Values, sites) is { } unavailable) return unavailable;
            if (reads.Count != 0)
            {
                // 读取可被整个返回项或整组写入消费；仍有外部使用时不删除它的定义。
                var roots = c.Snapshot.Blocks.SelectMany(b => b.Statements.Where(s => s is not MemoryRead
                    && !(s is Call call && call.Identity == consumedCall)
                    && !(s is MemoryWrite write && ids.Contains(write.Identity))).SelectMany(SnapshotRewrite.Uses)
                    .Concat(SnapshotRewrite.Uses(b.End)));
                var seen = new HashSet<Term>();
                bool Outside(Term value)
                {
                    var resolved = c.Get(state.Resolve, value); if (!resolved.IsSuccess) return true;
                    value = resolved.Value;
                    if (target is not null && value == target || !seen.Add(value)) return false;
                    if (reads.Any(r => r.Value == value)) return true;
                    return value.Operands.Any(Outside);
                }
                if (roots.Concat(sites.Where(s => !ids.Contains(s.Identity)).Select(s => s.Receiver).OfType<Term>()).Any(Outside)) return No("被覆盖的字段读取仍有返回项以外的使用");
                foreach (var read in reads)
                {
                    var occurrences = sites.Where(s => !s.Write && s.Value == read.Value).ToArray();
                    foreach (var occurrence in occurrences)
                    {
                        if (occurrence.Point == new Point(point.Block, begin)) continue;
                        var dominates = c.Get(flow.PointDominates, new(new Point(point.Block, begin), occurrence.Point));
                        if (!dominates.IsSuccess || !dominates.Value) return No("调用位置不支配同值读取");
                    }
                }
            }
            return null;
        }
    }
}
