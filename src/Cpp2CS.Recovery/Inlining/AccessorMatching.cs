using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Recovery.Inlining;

public sealed record AccessorReplacement(MethodRef Method, Term? Receiver, IReadOnlyList<Term> Arguments,
    Term? Result, Point Point, IReadOnlyList<ReadIdentity> Reads, IReadOnlyList<WriteIdentity> Writes);
public sealed record AccessorProgram(IReadOnlyList<AccessorReplacement> Replacements,
    IReadOnlyDictionary<StableIdentity, Reason> Failures);

public sealed partial class AccessorQuery
{
    public Outcome<AccessorProgram> Match(QueryContext context, MethodRef caller, StateQueries state,
        ManagedLocationQuery locations, IReadOnlyDictionary<Term, ManagedValue> arguments) =>
        context.Get(new ProgramQuery(types, templates, state, locations, caller, arguments, observe, Find), 0);

    private sealed record Site(Point Point, StableIdentity Identity, FieldRef Field, Term? Receiver, TypeRef? ReceiverType,
        Term Value, bool Write, ulong Address);
    private sealed record TemplateParameter(MethodDef Method, int Index) : AtomIdentity
    { public override string StableText => "inline.accessor-parameter"; }
    private sealed record CandidateMatch(AccessorReplacement Replacement, HashSet<Term> Coverage, Reason? Placement);

    /// <summary>只在一个基本块的直线范围发现；读取版本、支配和最终相等均取现有查询。</summary>
    private sealed class ProgramQuery(ManagedTypes types, IAccessorTemplateSource templates, StateQueries state,
        ManagedLocationQuery locations, MethodRef caller, IReadOnlyDictionary<Term, ManagedValue> arguments,
        Action<AccessorAttempt>? observe, Func<AccessorAccess, AccessorAnswer> Legacy) : Query<int, AccessorProgram>
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
                var group = window.Where(s => s.Write && s.Point.Before >= low && s.Receiver == anchor.Receiver).ToArray();
                foreach (var candidate in anchor.Field.Field.Owner.Methods.Where(m => m.Name is not (".ctor" or ".cctor")
                    && !m.IsOverridable
                    && m.GenericParameters.Count == 0 && (anchor.Write ? ManagedTypes.IsVoid(m.ReturnType) : !ManagedTypes.IsVoid(m.ReturnType))))
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
                    var values = template.Expression is { } expression ? new[] { expression }
                        : template.Stores.SelectMany(s => new[] { s.Target, s.Value }).ToArray();
                    var fieldNodes = values.SelectMany(ManagedValues.Walk).Where(v => FieldAccessor.FieldOf(v)?.Field == anchor.Field.Field).Distinct().ToArray();
                    foreach (var fieldNode in fieldNodes)
                    {
                        var fixedArgs = new Dictionary<int, Term>();
                        if (fieldNode is FieldValue { Receiver: ArgumentValue p })
                        { if (anchor.Receiver is null) continue; fixedArgs[p.Index] = anchor.Receiver; }
                        else if (fieldNode is not StaticFieldValue) continue;
                        if (!candidate.IsStatic && !fixedArgs.ContainsKey(-1)) continue;
                        Term?[] roots;
                        if (anchor.Write) roots = [null];
                        else if (Enumerable.Range(0, candidate.Parameters.Count).All(fixedArgs.ContainsKey))
                        {
                            var fixedInterpreter = new AccessorTerms(c.Snapshot.Terms, index => fixedArgs.GetValueOrDefault(index), (field, receiver) =>
                            {
                                var concrete = field with { DeclaringType = selected.Concrete(field.DeclaringType) };
                                var found = window.Where(s => !s.Write && s.Field.Equals(concrete) && s.Receiver == receiver).Select(s => s.Value).Distinct().ToArray();
                                return found is [var one] ? one : null;
                            });
                            var fixedTerm = fixedInterpreter.Read(template.Expression!);
                            if (fixedTerm is not null) fixedTerm = fixedInterpreter.Result(fixedTerm);
                            roots = fixedTerm is not null && allTerms.Contains(fixedTerm) ? [fixedTerm] : [];
                        }
                        else roots = allTerms.Where(t => t.Width <= 64 && !t.ContainsUndefined).Cast<Term?>().ToArray();
                        foreach (var target in roots)
                        {
                            var possible = target is null ? SnapshotRewrite.Dependencies(group.Select(s => s.Value)) : SnapshotRewrite.Dependencies([target]);
                            possible.UnionWith(arguments.Keys);
                            // 绑定只是发现；每一种完整代入仍须由最终项相等复核。
                            IEnumerable<Dictionary<int, Term>> Bind(int index, Dictionary<int, Term> bindings)
                            {
                                if (index == candidate.Parameters.Count) { yield return bindings; yield break; }
                                if (bindings.ContainsKey(index)) { foreach (var b in Bind(index + 1, bindings)) yield return b; yield break; }
                                var type = selected.Concrete(candidate.Parameters[index].Type);
                                int width = types.StorageBits(type);
                                if (width is <= 0 or > 64) yield break;
                                foreach (var term in possible.Where(t => t.Width == width && !t.ContainsUndefined
                                    && t.Kind is not (TermKind.Unknown or TermKind.Undefined)))
                                {
                                    var next = new Dictionary<int, Term>(bindings) { [index] = term };
                                    foreach (var b in Bind(index + 1, next)) yield return b;
                                }
                            }
                            foreach (var binding in Bind(0, fixedArgs))
                            {
                                if (c.Step() is { } why) return Outcome<AccessorProgram>.Failure(why);
                                var reads = new List<Site>(); bool uncertain = false;
                                var interpreter = new AccessorTerms(c.Snapshot.Terms, index => binding.GetValueOrDefault(index), (field, receiver) =>
                                {
                                    var concrete = field with { DeclaringType = selected.Concrete(field.DeclaringType) };
                                    var found = window.Where(s => !s.Write && s.Field.Equals(concrete) && s.Receiver == receiver).ToArray();
                                    if (found.Length == 0 || found.Select(s => s.Value).Distinct().Count() != 1) { uncertain = true; return null; }
                                    reads.AddRange(found); return found[0].Value;
                                });
                                var writes = new List<Site>();
                                if (target is not null)
                                {
                                    var expected = interpreter.Read(template.Expression!);
                                    if (expected is not null) expected = interpreter.Result(expected);
                                    if (expected != target || uncertain || !reads.Any(s => s.Identity == anchor.Identity)
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
                                var symbolic = new Dictionary<int, Term>(fixedArgs);
                                var free = new Dictionary<int, Term>();
                                foreach (int index in Enumerable.Range(0, candidate.Parameters.Count).Where(i => !fixedArgs.ContainsKey(i)))
                                {
                                    // 字段位置已精确绑定其对象；其余形参必须保留完整位的可逆约束。
                                    bool storageRoot = values.SelectMany(ManagedValues.Walk).OfType<FieldValue>()
                                        .Any(f => f.Receiver is ArgumentValue a && a.Index == index);
                                    if (storageRoot) symbolic[index] = binding[index];
                                    else symbolic[index] = free[index] = c.Snapshot.Terms.Atom(new TemplateParameter(candidate, index),
                                        types.StorageBits(selected.Concrete(candidate.Parameters[index].Type)));
                                }
                                var constraintReader = new AccessorTerms(c.Snapshot.Terms, index => symbolic.GetValueOrDefault(index), (field, receiver) =>
                                {
                                    var concrete = field with { DeclaringType = selected.Concrete(field.DeclaringType) };
                                    var found = window.Where(s => !s.Write && s.Field.Equals(concrete) && s.Receiver == receiver).Select(s => s.Value).Distinct().ToArray();
                                    return found is [var one] ? one : null;
                                });
                                var equations = target is not null ? new[] { constraintReader.Read(template.Expression!) }
                                    : template.Stores.Select(s => constraintReader.Read(s.Value) is { } value
                                        ? constraintReader.Resize(value, types.StorageBits(selected.Concrete(s.Target.Type))) : null).ToArray();
                                bool unique = free.Values.All(parameter => equations.OfType<Term>().Any(e => Determines(e, parameter)));
                                Reason? placement = unique ? Placement(c, block, included, point, binding, reads, target, sites)
                                    : new("inline.Accessor.Ambiguous", "形参的完整值没有可逆约束，存在未区分的实参代入");
                                var replacement = new AccessorReplacement(selected, candidate.IsStatic ? null : binding[-1],
                                    Enumerable.Range(0, candidate.Parameters.Count).Select(i => binding[i]).ToArray(), target, point,
                                    reads.Select(s => (ReadIdentity)s.Identity).ToArray(), writes.Select(s => (WriteIdentity)s.Identity).ToArray());
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
                var best = matches.Where(m => !matches.Any(other => other.Coverage.IsProperSupersetOf(m.Coverage))).ToArray();
                Reason? failure = best.Length > 1 ? new("inline.Accessor.Ambiguous", $"有 {best.Length} 个最大覆盖或不同实参代入，无法区分原调用")
                    : best.Length == 1 ? best[0].Placement
                    : new("inline.Accessor.None", candidates == 0 ? "没有候选" : incomplete.Count == candidates ? "候选未能完整恢复"
                        : shapes.Count != 0 ? string.Join("；", shapes.Order(StringComparer.Ordinal)) : "候选模板与完整项或写入组不匹配");
                var access = new AccessorAccess(caller, anchor.Address, anchor.Field, anchor.ReceiverType,
                    anchor.Write ? AccessorKind.Setter : AccessorKind.Getter, failure is null);
                if (best.Length == 1 && failure is null)
                {
                    var accepted = best[0].Replacement;
                    // 同一读取不能被两个不同调用消费。
                    if (accepted.Reads.Cast<StableIdentity>().Concat(accepted.Writes).Any(consumed.Contains))
                        failure = new("inline.Accessor.Ambiguous", "不同内联解释消费了同一次字段访问");
                    else
                    {
                        replacements.Add(accepted); consumed.UnionWith(accepted.Reads); consumed.UnionWith(accepted.Writes);
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
        private Reason? Placement(QueryContext c, Block block, Site[] included, Point point, Dictionary<int, Term> binding,
            List<Site> reads, Term? target, List<Site> sites)
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
            foreach (var term in binding.Values)
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
                    if (dependency.Identity is ResultAtom { Definition: MergeIdentity } or MemoryMerge)
                        return No("实参的合流定义尚未证明支配调用位置");
                }
            if (reads.Count != 0)
            {
                // 读取可被整个返回项或整组写入消费；仍有外部使用时不删除它的定义。
                var roots = c.Snapshot.Blocks.SelectMany(b => b.Statements.Where(s => s is not MemoryRead
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
                if (roots.Any(Outside)) return No("被覆盖的字段读取仍有返回项以外的使用");
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
