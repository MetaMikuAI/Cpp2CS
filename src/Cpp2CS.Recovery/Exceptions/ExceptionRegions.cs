using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Recovery.Structure;

namespace Cpp2CS.Recovery.Exceptions;

public sealed record ExceptionClausePlan(BlockIdentity Source, TypeRef Type, BlockIdentity Entry, ImmutableHashSet<BlockIdentity> Body)
{
    public FinallyPlan? Finally { get; init; }
}
public sealed record ExceptionRegionPlan(BlockIdentity Source, BlockIdentity Entry, ImmutableHashSet<BlockIdentity> Try, ImmutableArray<ExceptionClausePlan> Clauses);
public sealed record ExceptionPlan(ImmutableArray<ExceptionRegionPlan> Regions, ImmutableArray<BlockIdentity> Order,
    ImmutableHashSet<BlockIdentity> Removed, ImmutableHashSet<CallIdentity> PrivateCalls, ImmutableHashSet<WriteIdentity> PrivateWrites,
    ImmutableDictionary<CallIdentity, BlockIdentity> Rethrows,
    ImmutableDictionary<CallIdentity, BlockIdentity?> Unwind);

/// <summary>处理入口的私有状态与子句分类先于区域构造；区域只查询，不复制或移动调用。</summary>
public sealed partial class ExceptionRegionQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names,
    RuntimeSpec spec, TypeRef objectType, bool nested = false, bool projected = false) : Query<int, ExceptionPlan>
{
    private readonly FlowQueries flow = new();
    private readonly PathFactQuery facts = new(state);
    public override Outcome<ExceptionPlan> Compute(QueryContext c, int key)
    {
        Outcome<ExceptionPlan> No(string code, string message, Reason? cause = null) =>
            Outcome<ExceptionPlan>.Failure(new("lowering.Exception." + code, message, cause));
        var f = c.Snapshot;
        if (!projected)
        {
            var semantic = ExceptionScaffolding.Project(f, calls);
            if (!ReferenceEquals(semantic, f))
            {
                var result = names.CreateContext(semantic).Get(new ExceptionRegionQuery(state, calls, names, spec, objectType, nested, true), 0);
                return result.IsSuccess ? Outcome<ExceptionPlan>.Success(result.Value with
                { Removed = result.Value.Removed.Union(f.Blocks.Select(b => b.Identity).Except(semantic.Blocks.Select(b => b.Identity))) }) : result;
            }
        }
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return No("State", "展开状态索引不可用", index.Why);
        var blocks = index.Value.Blocks;
        var handlers = f.Blocks.Where(b => b.Handler is not null).ToArray();
        var selectorFailures = ExceptionSelectors.Run(f, spec).Failures;
        if (selectorFailures.Count != 0) return Outcome<ExceptionPlan>.Failure(selectorFailures.Values.First());
        var dominance = new Dominance(f);
        bool Dominates(BlockIdentity a, BlockIdentity b) => a == b || dominance.StrictlyDominates(a, 0, b, 0);
        var scopes = new Dictionary<BlockIdentity, HashSet<BlockIdentity>>();
        foreach (var h in handlers)
        {
            var body = new HashSet<BlockIdentity>();
            foreach (var b in f.Blocks)
            {
                if (Dominates(h.Identity, b.Identity)) body.Add(b.Identity);
            }
            scopes[h.Identity] = body;
        }
        var classified = new Dictionary<CallIdentity, ClassifiedCall>();
        var privateCalls = new HashSet<CallIdentity>();
        var privateWrites = new HashSet<WriteIdentity>();
        foreach (var call in f.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            var result = c.Get(calls, call.Identity); if (!result.IsSuccess) return No("State", "异常调用身份查询失败", result.Why);
            classified.Add(call.Identity, result.Value);
            if (result.Value.Operation?.Name is "BeginCatch" or "EndCatch" or "CxxGetExceptionPointer" or "CxxFreeException") privateCalls.Add(call.Identity);
        }
        // 活跃性沿合流传递；未绑定的原生槽位不属于托管语义使用。
        var selectorUses = new StructureLiveness(f, SnapshotRewrite.Uses, statementUses: statement => statement switch
        {
            Call call => (classified[call.Identity].Inputs?.Values.SelectMany(v => v.Source is TermSource t ? new[] { t.Term } : Array.Empty<Term>()) ?? [])
                .Concat(call.Target is ComputedTarget target ? [target.Value] : [])
                .Concat(call.OutgoingArgumentArea is { } area ? [area] : []),
            _ => SnapshotRewrite.Uses(statement),
        });
        if (handlers.Any(h => selectorUses.Used(h.Handler!.Selector)))
            return No("Selector", "选择值存在未折叠的测试或其他语义用法");
        bool Private(Statement s) => s switch
        {
            MemoryRead => true,
            MemoryWrite w when privateWrites.Contains(w.Identity) => true,
            // 帧写入不能仅凭帧地址判为私有；只接受已证明属于异常私有存储的写入。
            MemoryWrite => false,
            Call call => privateCalls.Contains(call.Identity),
            _ => false,
        };
        var edgeValues = new EdgeValueQuery(state);
        var resumes = new Dictionary<BlockIdentity, HashSet<BlockIdentity>>();
        bool SameResume(Term value, BlockIdentity handler) =>
            c.Get(names, value) is { IsSuccess: true, Value.Name: ExceptionPointerName pointer } && pointer.Handler == handler;
        var transparent = handlers.Where(h =>
        {
            var scope = scopes[h.Identity]; var shared = new HashSet<BlockIdentity>();
            if (scope.Count == 0 || scope.Any(id => !blocks[id].Statements.All(Private) || blocks[id].End is not (Jump or ResumeUnwind))) return false;
            foreach (var id in scope)
            {
                if (blocks[id].End is ResumeUnwind resume && !SameResume(resume.Exception, h.Identity)) return false;
                foreach (var target in SnapshotRewrite.Targets(blocks[id].End).Where(to => !scope.Contains(to)))
                {
                    if (blocks[target].End is not ResumeUnwind tail || !blocks[target].Statements.All(Private)) return false;
                    var value = c.Get(edgeValues, new(tail.Exception, new(id, target)));
                    if (!value.IsSuccess || !SameResume(value.Value, h.Identity)) return false;
                    shared.Add(target);
                }
            }
            if (shared.Count == 0 && !scope.Any(id => blocks[id].End is ResumeUnwind)) return false;
            resumes.Add(h.Identity, shared); return true;
        }).Select(h => h.Identity).ToHashSet();
        var removed = transparent.SelectMany(h => scopes[h]).ToHashSet();
        foreach (var tail in resumes.Values.SelectMany(ids => ids).Distinct())
            if (index.Value.Predecessors[tail].All(p => removed.Contains(p.Block))) removed.Add(tail);
        var unwind = new Dictionary<CallIdentity, BlockIdentity?>();
        // 透明清理若仍由外层保护，必须保留该外层；没有唯一外层时拒绝折叠。
        foreach (var call in f.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            var target = call.Unwind;
            var visited = new HashSet<BlockIdentity>();
            while (target is not null && transparent.Contains(target))
            {
                if (!visited.Add(target)) return No("Region", "透明处理入口的外层关系成环");
                var outer = scopes[target].SelectMany(id => blocks[id].Statements).OfType<Call>()
                    .Where(x => x.Unwind is not null && !scopes[target].Contains(x.Unwind!)).Select(x => x.Unwind!).Distinct().ToArray();
                if (outer.Length > 1) return No("Region", "透明处理入口没有唯一的外层处理入口");
                target = outer.SingleOrDefault();
            }
            unwind[call.Identity] = target;
        }
        var opaque = handlers.Where(h => !transparent.Contains(h.Identity)).ToArray();
        if (opaque.Length > 1)
        {
            var entries = ExceptionEntries.Run(f);
            if (!entries.Reasons.IsEmpty) return No("Entries", "多个处理入口汇合不能归一：" + string.Join("；", entries.Reasons));
            if (!nested) return No("Nested", "存在多个不透明处理入口，当前阶段只支持一个");
        }
        var callBlocks = f.Blocks.SelectMany(block => block.Statements.OfType<Call>().Select(call => (call.Identity, block.Identity)))
            .ToDictionary(pair => pair.Item1, pair => pair.Item2);
        var owners = f.Blocks.ToDictionary(block => block.Identity, block => opaque.Where(h => scopes[h.Identity].Contains(block.Identity))
            .OrderBy(h => scopes[h.Identity].Count).Select(h => h.Identity).FirstOrDefault());
        var rethrows = new Dictionary<CallIdentity, BlockIdentity>();
        var plans = new List<ExceptionRegionPlan>();
        foreach (var h in opaque)
        {
            var scope = scopes[h.Identity];
            foreach (var call in scope.SelectMany(id => blocks[id].Statements).OfType<Call>())
            {
                if (owners[callBlocks[call.Identity]] != h.Identity) continue;
                var named = classified[call.Identity];
                if (named.Operation?.Name == "CxxRethrow") rethrows[call.Identity] = h.Identity;
                if (named.Operation?.Name == "CxxThrow" && named.Inputs?.GetValueOrDefault("exception")?.Source is TermSource payload
                    && named.Inputs?.GetValueOrDefault("type")?.Source is TermSource thrownType)
                {
                    var resolved = c.Get(state.Resolve, payload.Term);
                    var typeValue = c.Get(state.Resolve, thrownType.Term);
                    if (resolved.IsSuccess && typeValue.IsSuccess && resolved.Value.Identity is ResultAtom { Definition: CallIdentity allocation }
                        && classified.TryGetValue(allocation, out var allocated) && allocated.Operation?.Name == "CxxAllocateException"
                        && allocated.Inputs?.GetValueOrDefault("size")?.Source is TermSource size
                        && c.Get(state.Resolve, size.Term) is { IsSuccess: true, Value.ConstantValue: { } bytes }
                        && bytes == spec.Layout.Record("Il2CppExceptionWrapper").Size)
                    {
                        var target = c.Get(state.Locations, new(typeValue.Value, f.AddressWidth));
                        bool sameType = target.IsSuccess && target.Value.Region == Region.Image && target.Value.Offset is { } offset
                            && h.Handler!.Clauses.SelectMany(clause => clause.Matches).OfType<PointerTarget.Internal>().Any(p => p.Offset == offset);
                        if (sameType)
                        {
                            var owner = f.Blocks.Single(b => b.Statements.Contains(call));
                            var field = spec.Layout.Field("Il2CppExceptionWrapper", "ex");
                            var contents = c.Get(state.ValueAt, new(new(owner.Identity, owner.Statements.IndexOf(call)), new(Region.Other, resolved.Value, field.ByteOffset, f.AddressWidth)));
                            if (contents.IsSuccess && c.Get(names, contents.Value) is { IsSuccess: true, Value.Name: CaughtExceptionName caughtPayload }
                                && caughtPayload.Handler == h.Identity)
                            {
                                rethrows[call.Identity] = h.Identity;
                                privateCalls.Add(allocation);
                                foreach (var write in f.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>())
                                {
                                    var address = c.Get(state.Resolve, write.Address);
                                    if (!address.IsSuccess) continue;
                                    var location = c.Get(state.Locations, new(address.Value, write.Width));
                                    if (location.IsSuccess && location.Value is { Region: Region.Other, Offset: { } at } && location.Value.Root == resolved.Value
                                        && at == field.ByteOffset && write.Width == f.AddressWidth) privateWrites.Add(write.Identity);
                                }
                            }
                        }
                    }
                }
                if (named.Operation?.Name == "Rethrow" && named.Inputs?.GetValueOrDefault("exception")?.Source is TermSource input
                    && c.Get(names, input.Term) is { IsSuccess: true, Value.Name: CaughtExceptionName caught } && caught.Handler == h.Identity)
                    rethrows[call.Identity] = h.Identity;
            }
            var typeTests = new Dictionary<BlockIdentity, (TypeRef Type, BlockIdentity Accepted, BlockIdentity Rejected, CallIdentity Call)>();
            bool hasTypeTest = scope.SelectMany(id => blocks[id].Statements).OfType<Call>().Any(call => classified[call.Identity].Operation?.Name == "IsAssignableFrom");
            foreach (var id in scope.Where(_ => hasTypeTest))
                if (blocks[id].End is Branch && TypeTest(c, blocks[id], h.Identity, classified, out var targetType, out var yes, out var no, out var identity))
                {
                    typeTests.Add(id, (targetType!, yes!, no!, identity!));
                    privateCalls.Add(identity!);
                }
            var prefix = new HashSet<BlockIdentity>();
            var clauses = new List<ExceptionClausePlan>();
            var cursor = h.Identity;
            var seen = new HashSet<BlockIdentity>();
            bool begun = false;
            while (seen.Add(cursor))
            {
                var block = blocks[cursor];
                begun |= block.Statements.OfType<Call>().Any(call => classified[call.Identity].Operation?.Name == "BeginCatch"
                    && classified[call.Identity].Result?.Source is TermSource result
                    && c.Get(names, result.Term) is { IsSuccess: true, Value.Name: ExceptionPayloadName p } && p.Handler == h.Identity);
                if (block.End is Jump jump && scope.Contains(jump.Target) && block.Statements.All(Private))
                { prefix.Add(cursor); cursor = jump.Target; continue; }
                if (block.End is Branch && typeTests.TryGetValue(cursor, out var typeTest))
                {
                    if (block.Statements.Any(s => !Private(s) && (s is not Call call || call.Identity != typeTest.Call)))
                        return No("Filter", "类型选择之前存在可观察操作");
                    prefix.Add(cursor);
                    var body = scope.Where(id => Dominates(typeTest.Accepted, id)).ToImmutableHashSet();
                    if (body.Count == 0) return No("Region", "类型子句没有唯一入口");
                    clauses.Add(new(h.Identity, typeTest.Type, typeTest.Accepted, body)); cursor = typeTest.Rejected; continue;
                }
                if (block.End is Branch branchEnd)
                {
                    var condition = c.Get(state.Resolve, branchEnd.Condition);
                    if (!condition.IsSuccess) return No("State", "处理入口条件没有可用状态", condition.Why);
                    if (SnapshotRewrite.Dependencies([condition.Value]).Any(t => t.Identity is SelectorAtom))
                        return No("Selector", "原生子句选择值尚未证明只选择托管包装类型");
                }
                break;
            }
            if (!begun) return No("Fault", "不透明处理入口未取得托管包装异常；fault 或原生处理形状尚未支持");
            var shared = clauses.Count == 0 ? SharedFinally(c, h.Identity, scope, classified, Private, unwind) : null;
            if (shared is not null)
            {
                clauses.Add(new(h.Identity, objectType, shared.Entry, shared.Body) { Finally = shared });
                prefix.UnionWith(shared.Removed);
            }
            else if (clauses.Count == 0)
            {
                // 全捕获保留主体全部事件；仅跳板与私有前缀没有对应的 IL。
                var body = scope.Except(prefix).ToImmutableHashSet();
                clauses.Add(new(h.Identity, objectType, cursor, body));
            }
            else
            {
                var tail = scope.Except(prefix).Except(clauses.SelectMany(x => x.Body)).ToArray();
                if (tail.Any(id => !blocks[id].Statements.All(s => Private(s) || s is Call call && rethrows.ContainsKey(call.Identity))
                    || blocks[id].End is not (Jump or Unreachable or ResumeUnwind))
                    || !tail.SelectMany(id => blocks[id].Statements).OfType<Call>().Any(call => rethrows.ContainsKey(call.Identity)))
                    return No("Filter", "类型判断的未命中路径不是只重新抛出");
                prefix.UnionWith(tail);
            }
            for (int i = 0; i < clauses.Count; i++)
                for (int j = i + 1; j < clauses.Count; j++)
                    if (clauses[i].Body.Overlaps(clauses[j].Body)) return No("Region", "不同 catch 子句共用了处理块");
            removed.UnionWith(prefix);
            var throwing = f.Blocks.Where(b => !removed.Contains(b.Identity) && b.Statements.OfType<Call>().Any(call => !privateCalls.Contains(call.Identity) && unwind[call.Identity] == h.Identity)).Select(b => b.Identity).ToHashSet();
            if (throwing.Count == 0) return No("Region", "处理入口没有受保护的调用");
            var starts = shared is null ? throwing : throwing.Union(shared.Arrivals).ToHashSet();
            var dominators = f.Blocks.Where(b => !scope.Contains(b.Identity) && starts.All(t => Dominates(b.Identity, t))).Select(b => b.Identity).ToArray();
            var entry = dominators.FirstOrDefault(d => dominators.All(a => Dominates(a, d)));
            if (entry is null) return No("Region", "受保护调用不存在共同的单入口");
            var members = new HashSet<BlockIdentity>(starts) { entry };
            var work = new Stack<BlockIdentity>(starts);
            while (work.TryPop(out var id))
            {
                if (c.Step() is { } budget) return No("Region", "区域构造预算耗尽", budget);
                foreach (var from in index.Value.Predecessors[id])
                    if (!scope.Contains(from.Block) && Dominates(entry, from.Block)
                        && members.Add(from.Block)) work.Push(from.Block);
            }
            foreach (var id in members)
            {
                if (scope.Contains(id)) return No("Backedge", "处理体跳回 try 内部");
                if (id != entry && index.Value.Predecessors[id].Any(p => !members.Contains(p.Block)))
                    return No("MultiEntry", "try 中间存在区域外入边");

            }
            foreach (var clause in clauses)
            {
                if (!clause.Body.Contains(clause.Entry)) return No("Region", "catch 入口不在处理区域内");
                if (clause.Finally is null && clause.Body.Any(id => index.Value.Predecessors[id].Any(p => !clause.Body.Contains(p.Block) && !prefix.Contains(p.Block))))
                    return No("Region", "catch 有类型选择之外的入边");
                if (clause.Body.SelectMany(id => SnapshotRewrite.Targets(blocks[id].End)).Any(members.Contains))
                    return No("Backedge", "处理体跳回 try 内部");
            }
            if (shared is not null && members.Any(id => blocks[id].End is Return or ResumeUnwind
                || SnapshotRewrite.Targets(blocks[id].End).Any(to => !members.Contains(to) && to != shared.Entry)))
                return No("Finally.Region", "共享清理之前存在其他正常出口");
            if (shared is null && clauses.Count == 1 && clauses[0].Type.Equals(objectType)
                && CopiedFinally(c, clauses[0], members, classified, Private, rethrows, removed, unwind, dominance) is { } copied)
            {
                clauses[0] = clauses[0] with { Body = copied.Body, Finally = copied };
                removed.UnionWith(copied.Removed);
                foreach (var statement in copied.Omitted)
                {
                    if (statement is Call call) { privateCalls.Add(call.Identity); rethrows.Remove(call.Identity); }
                    else if (statement is MemoryWrite write) privateWrites.Add(write.Identity);
                }
            }
            plans.Add(new(h.Identity, entry, members.ToImmutableHashSet(), clauses.ToImmutableArray()));
        }
        // 先剔除私有前缀，再把完整的内层区域纳入它所在的外层 try。
        plans = plans.Select(p => p with { Try = p.Try.Except(removed).ToImmutableHashSet(), Clauses = p.Clauses
            .Select(clause => clause with { Body = clause.Body.Except(removed).ToImmutableHashSet() }).ToImmutableArray() }).ToList();
        var extents = new Dictionary<ExceptionRegionPlan, ImmutableHashSet<BlockIdentity>>();
        ImmutableHashSet<BlockIdentity> Whole(ExceptionRegionPlan p)
        {
            if (!extents.TryGetValue(p, out var extent)) extents.Add(p, extent = p.Try.Union(p.Clauses.SelectMany(clause => clause.Body)));
            return extent;
        }
        bool enlarged;
        do
        {
            enlarged = false;
            for (int i = 0; i < plans.Count; i++)
                for (int j = 0; j < plans.Count; j++)
                {
                    if (i == j || plans[i].Try.SetEquals(plans[j].Try)) continue;
                    var inside = Whole(plans[j]);
                    if ((plans[j].Try.IsSubsetOf(plans[i].Try) || plans[j].Clauses.Any(clause => clause.Finally?.PropagatesTo == plans[i].Source))
                        && !inside.IsSubsetOf(plans[i].Try))
                    { plans[i] = plans[i] with { Try = plans[i].Try.Union(inside) }; enlarged = true; }
                    ImmutableArray<ExceptionClausePlan>.Builder? clauses = null;
                    for (int k = 0; k < plans[i].Clauses.Length; k++)
                    {
                        var clause = plans[i].Clauses[k];
                        if (!plans[j].Try.IsSubsetOf(clause.Body) || inside.IsSubsetOf(clause.Body)) continue;
                        enlarged = true; var body = clause.Body.Union(inside);
                        clauses ??= plans[i].Clauses.ToBuilder();
                        clauses[k] = clause with { Body = body, Finally = clause.Finally is { } plan ? plan with { Body = body } : null };
                    }
                    if (clauses is not null) plans[i] = plans[i] with { Clauses = clauses.ToImmutable() };
                }
        } while (enlarged);
        for (int i = 0; i < plans.Count; i++)
        {
            var candidates = plans[i].Try.Where(id => plans[i].Try.All(member => Dominates(id, member))).ToArray();
            var entry = candidates.FirstOrDefault(id => candidates.All(other => Dominates(other, id)));
            if (entry is null) return No("Region", "扩张后的 try 没有共同入口");
            plans[i] = plans[i] with { Entry = entry };
        }
        if (plans.Any(p => p.Clauses.Any(clause => p.Try.Overlaps(clause.Body))))
            return No("Region", "try 与自身的 catch 处理体相交");
        var segments = plans.SelectMany(p => new[] { (Owner: p, Members: p.Try, Entry: p.Entry) }
            .Concat(p.Clauses.Select(clause => (Owner: p, Members: clause.Body, Entry: clause.Entry)))).ToArray();
        foreach (var segment in segments)
            if (segment.Members.Count == 0 || !segment.Members.Contains(segment.Entry)) return No("Region", "区域的入口被私有前缀折叠");
        for (int i = 0; i < plans.Count; i++)
            for (int j = i + 1; j < plans.Count; j++)
            {
                var a = Whole(plans[i]); var b = Whole(plans[j]);
                if (!a.Overlaps(b)) continue;
                if (plans[i].Try.SetEquals(plans[j].Try)) return No("Entries", "同一 try 的多个逻辑入口缺少共同的原生子句次序");
                if (!segments.Any(s => s.Owner == plans[i] && b.IsSubsetOf(s.Members))
                    && !segments.Any(s => s.Owner == plans[j] && a.IsSubsetOf(s.Members)))
                    return No("Region", "异常区域部分相交或跨过 try 与处理体边界");
            }
        foreach (var p in plans)
        {
            foreach (var clause in p.Clauses.Where(clause => clause.Finally is not null))
                if (clause.Body.Any(id => id != clause.Entry && index.Value.Predecessors[id].Any(edge => !clause.Body.Contains(edge.Block) && !removed.Contains(edge.Block))))
                    return No("Finally.Region", "清理体中间存在区域外入边");
            foreach (var id in p.Try)
            {
                if (id != p.Entry && index.Value.Predecessors[id].Any(edge => !p.Try.Contains(edge.Block) && !removed.Contains(edge.Block)))
                    return No("MultiEntry", "try 中间存在区域外入边");
                foreach (var call in blocks[id].Statements.OfType<Call>().Where(call => !privateCalls.Contains(call.Identity)))
                {
                    var target = unwind[call.Identity];
                    if (target == p.Source || target is null && classified[call.Identity].Operation?.Exceptions.MayThrow == false) continue;
                    var child = plans.SingleOrDefault(inner => inner.Source == target);
                    if (child is null || !Whole(child).IsSubsetOf(p.Try)) return No("Region", "try 扩张会改变某个调用的处理入口");
                }
            }
        }
        // 每个内层区域完整地位于一个 try 或一个 catch 中；按这个包含关系布局连续的块区间。
        var parents = plans.ToDictionary(p => p, p => segments.Where(s => s.Owner != p && Whole(p).IsSubsetOf(s.Members))
            .OrderBy(s => s.Members.Count).Select(s => s.Members).FirstOrDefault());
        var order = new List<BlockIdentity>(); var emitted = new HashSet<BlockIdentity>();
        void Container(ImmutableHashSet<BlockIdentity> members, BlockIdentity first)
        {
            foreach (var block in f.Blocks.OrderByDescending(b => b.Identity == first))
            {
                if (!members.Contains(block.Identity) || emitted.Contains(block.Identity)) continue;
                var child = plans.FirstOrDefault(p => parents[p] == members && Whole(p).Contains(block.Identity));
                if (child is null) { emitted.Add(block.Identity); order.Add(block.Identity); continue; }
                Container(child.Try, child.Entry);
                foreach (var clause in child.Clauses) Container(clause.Body, clause.Entry);
            }
        }
        var root = f.Blocks.Select(b => b.Identity).Except(removed).ToImmutableHashSet();
        foreach (var p in plans.Where(p => parents[p] is null)) parents[p] = root;
        Container(root, f.Entry);
        if (order.Count != root.Count) return No("Region", "异常区域布局没有覆盖全部保留块");
        return Outcome<ExceptionPlan>.Success(new(plans.OrderBy(p => Whole(p).Count).ToImmutableArray(), order.ToImmutableArray(), removed.ToImmutableHashSet(), privateCalls.ToImmutableHashSet(), privateWrites.ToImmutableHashSet(), rethrows.ToImmutableDictionary(), unwind.ToImmutableDictionary()));
    }

    private bool TypeTest(QueryContext c, Block block, BlockIdentity handler, Dictionary<CallIdentity, ClassifiedCall> classified,
        out TypeRef? type, out BlockIdentity? accepted, out BlockIdentity? rejected, out CallIdentity? test)
    {
        type = null; accepted = rejected = null; test = null;
        var branch = (Branch)block.End;
        var condition = c.Get(state.Resolve, branch.Condition);
        if (!condition.IsSuccess) return false;
        var dependencies = SnapshotRewrite.Dependencies([condition.Value]);
        foreach (var identity in dependencies.Select(t => t.Identity).OfType<ResultAtom>().Select(a => a.Definition).OfType<CallIdentity>().Distinct())
        {
            if (!classified.TryGetValue(identity, out var named)) continue;
            if (named.Operation?.Name != "IsAssignableFrom" || named.Result?.Source is not TermSource result
                || named.Inputs?.GetValueOrDefault("class")?.Source is not TermSource target
                || named.Inputs?.GetValueOrDefault("candidate")?.Source is not TermSource candidate) continue;
            var actual = c.Get(names, candidate.Term); var wanted = c.Get(names, target.Term);
            if (!actual.IsSuccess || actual.Value.Name is not FieldName { Owner: CaughtExceptionName caught, Record: "Il2CppObject", Field: var field }
                || caught.Handler != handler || field != spec.Layout.Field("Il2CppObject", "klass").Path
                || !wanted.IsSuccess || wanted.Value.Name is not EntityName { Entity: ClassEntity entity }) continue;
            var bit = c.Snapshot.Terms.Slice(result.Term, 0, 1);
            var nonzero = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, bit, c.Snapshot.Terms.Constant(0, 1));
            var onTrue = c.Get(facts, new(new(block.Identity, block.Statements.Length), nonzero, new(block.Identity, branch.True)));
            if (!onTrue.IsSuccess || onTrue.Value == PathTruth.Unknown) continue;
            type = entity.Type; test = identity;
            accepted = onTrue.Value == PathTruth.True ? branch.True : branch.False;
            rejected = onTrue.Value == PathTruth.True ? branch.False : branch.True;
            return true;
        }
        return false;
    }
}
