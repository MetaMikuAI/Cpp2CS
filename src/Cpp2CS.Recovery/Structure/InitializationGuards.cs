using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private NativeFunction FoldInitializationGuards(NativeFunction input, List<StructureRecord> records, QueryContext context, out HashSet<BlockIdentity> retainedGuards, out QueryContext finalContext, ref bool assumed)
    {
        var rejected = new Dictionary<ReadIdentity, StructureRecord>();
        var rejectedHeads = new Dictionary<ReadIdentity, BlockIdentity>();
        while (true)
        {
            var tests = input.Blocks.Where(b => b.End is Branch).Select(b => (Head: b, Test: InitializationTest.Of(((Branch)b.End).Condition)))
                .Where(x => x.Test is not null).ToArray();
            if (tests.Length == 0) break;
            var c = context = ReferenceEquals(context.Snapshot, input) ? context : names.CreateContext(input);
            var reads = input.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().ToDictionary(r => r.Identity);
            SemanticUses? uses = null;
            var prefix = new InitializationPrefixQuery(state, calls, names, image);
            bool changed = false;
            var batch = new SnapshotRewrite(input);
            var occupied = new HashSet<BlockIdentity>();
            var owners = input.Blocks.SelectMany(b => b.Statements.Select(statement => (statement, b.Identity))).ToDictionary(x => x.statement, x => x.Identity);
            var originalBlocks = input.Blocks.ToDictionary(b => b.Identity);
            foreach (var (head, test) in tests)
            {
                if (occupied.Contains(head.Identity)) continue;
                var branch = (Branch)head.End;
                if (test is null || !reads.TryGetValue(test.Read, out var read)) continue;
                var address = c.Get(state.Resolve, read.Address);
                var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, read.Width)) : default;
                if (!location.IsSuccess) continue;
                ulong? cacheAddress = read.Width == input.AddressWidth && location.Value is { Region: Region.Image, Offset: { } cacheOffset }
                    && cacheOffset >= 0 && cacheOffset <= ulong.MaxValue ? (ulong)cacheOffset : null;
                var cacheForwarder = cacheAddress is { } cacheKey ? internalCalls?.Caches.GetValueOrDefault(cacheKey) : null;
                var cacheMethod = cacheForwarder?.Method ?? (cacheAddress is not null ? discoverInternalCall : null);
                bool cache = cacheMethod is not null;
                // 缓存调用重绑定使用完整删边后的快照；先提交本批已有编辑，再在新快照上处理。
                if (cache && changed) continue;
                bool methodFlag = read.Width == 8 && location.Value is { Region: Region.Image, Offset: { } offset } && offset >= 0 && offset <= ulong.MaxValue && names.Flags.ContainsKey((ulong)offset);
                if (!cache && !methodFlag && (location.Value.Region != Region.Other || !InitializationStateWidths.Contains(read.Width))) continue;
                FieldName? field = null;
                if (!cache && !methodFlag)
                {
                    var storage = input.Terms.Atom(new MemoryAtom(location.Value, null), read.Width);
                    var named = c.Get(names, input.Terms.Slice(storage, test.Low, test.Width));
                    field = named.IsSuccess && named.Value.Name is FieldName value ? value : null;
                    if (field is null && read.Width == input.AddressWidth && (test.Low != 0 || test.Width != read.Width)
                        && c.Get(names, storage) is { IsSuccess: true, Value.Name: FieldName { Record: "MethodInfo" } whole }) field = whole;
                }
                bool stateField = field is not null && InitializationStateFields.Contains(field.Field);
                bool classFlag = stateField && field!.Record == "Il2CppClass";
                bool methodContext = stateField && field!.Record == "MethodInfo";
                if (!stateField && !methodFlag && !cache) continue;
                void Reject(Reason why)
                {
                    rejected[read.Identity] = new("init-guard", read.Trace?.NativeAddress, why.Message, false) { Reason = why };
                    rejectedHeads[read.Identity] = head.Identity;
                }
                // 类型含本定义的类型参数时，类来自泛型上下文；封闭的类实体照常改写。
                if (classFlag && field!.Owner is EntityName { Entity: ClassEntity { Type: var guarded } } && guarded.ContainsGenericParameter()
                    || classFlag && field!.Owner is ParameterName { MethodInformation: true })
                { Reject(new("structure.init-guard.generic-context", "类来自当前泛型上下文，本变换不处理该来源。")); continue; }
                if (classFlag && field!.Owner is not EntityName { Entity: ClassEntity })
                { Reject(new("structure.init-guard.class-unnamed", "初始化状态的类没有实体凭据或来自泛型上下文。")); continue; }
                if (methodContext && (field!.Owner is not (EntityName { Entity: MethodEntity } or ParameterName { MethodInformation: true })
                    || !names.ContextEntity(field.Owner)))
                { Reject(new("structure.init-guard.method-unnamed", "初始化状态的方法没有已命名的实体或当前定义的泛型上下文凭据。")); continue; }
                if (methodContext && (test.Low != 0 || test.Width != read.Width))
                { Reject(new("structure.init-guard.test-width", "泛型上下文指针没有按完整宽度测试零或非零。")); continue; }
                if (cache && (test.Low != 0 || test.Width != read.Width || read.Acquire
                    || image.Query(cacheAddress!.Value) is not { Writable: true, Executable: false } cacheStorage
                    || cacheStorage.Storage == Cpp2CS.Native.Images.StorageKind.Unmapped || cacheStorage.AvailableBytes < (ulong)(read.Width / 8)))
                { Reject(new("structure.init-guard.icall-storage", "内部调用缓存缺少完整指针零测试或可写数据位置凭据。")); continue; }
                var flag = methodFlag ? names.Flags.GetValueOrDefault((ulong)location.Value.Offset!.Value) : null;
                Reason? flagFailure = methodFlag && flag?.IsFlag != true ? new("structure.init-guard.flag-evidence", "本函数未证明该字节是方法元数据初始化标志。",
                    Chain(flag?.Reasons ?? [new("naming.no-access-evidence", "本函数没有该字节的访问凭据。")])) : null;
                uses ??= new(c, calls, state, names.Binder, names.Entry);
                bool otherUses = uses.Of(read.Identity).Any(use => !use.Condition || use.Point != new Point(head.Identity, head.Statements.Length));
                var eventId = test.ZeroWhenTrue ? branch.True : branch.False;
                var group = c.Get(prefix, new(new(head.Identity, eventId), stateField ? field : null,
                    methodFlag || cache ? location.Value : null, test.Low, test.Width, cacheMethod));
                if (!group.IsSuccess) { Reject(Append(group.Why!, flagFailure)); continue; }
                if (flagFailure is not null) { Reject(flagFailure); continue; }
                var moved = group.Value.Statements;
                var region = moved.Select(statement => owners[statement]).Append(head.Identity).Append(group.Value.After.Block)
                    .Concat(moved.OfType<Call>().Where(call => call.Unwind is not null).Select(call => call.Unwind!)).ToHashSet();
                if (region.Overlaps(occupied)) continue;
                var edit = new SnapshotRewrite(input);
                var tail = edit.Blocks[group.Value.After.Block];
                bool unwindValid = true;
                foreach (var call in moved.OfType<Call>().Where(call => call.Unwind is not null))
                {
                    var source = input.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == call.Identity));
                    var handler = edit.Blocks[call.Unwind!];
                    var merges = ImmutableArray.CreateBuilder<Merge>();
                    foreach (var merge in handler.Merges)
                    {
                        var incoming = merge.Inputs.Single(i => i.Predecessor == source.Identity);
                        var existing = merge.Inputs.FirstOrDefault(i => i.Predecessor == head.Identity);
                        if (existing is not null && existing.Value != incoming.Value) { unwindValid = false; break; }
                        merges.Add(existing is null ? merge with { Inputs = merge.Inputs.Add(new(head.Identity, incoming.Value)) } : merge);
                    }
                    if (!unwindValid) break;
                    edit.Blocks[handler.Identity] = handler with { Merges = merges.ToImmutable() };
                }
                if (!unwindValid)
                { Reject(new("structure.init-guard.unwind-merge", "移动调用的展开边与入口处已有的异常合流值不一致。")); continue; }
                bool candidateAssumed = assumed;
                RefineGuardResults(c, edit, moved.OfType<Call>(), ref candidateAssumed);
                edit.Blocks[tail.Identity] = tail with { Statements = tail.Statements.Skip(group.Value.After.Before).ToImmutableArray() };
                edit.Blocks[head.Identity] = head with { Statements = head.Statements.AddRange(moved), End = new Jump(tail.Identity) };
                if (otherUses && InitializationReadUses(c, edit, read, field, group.Value) is { } useFailure)
                { Reject(Append(useFailure, flagFailure)); continue; }
                if (cache && FoldInternalCallCache(c, edit, read, location.Value, group.Value, cacheForwarder, cacheMethod!) is { } cacheFailure)
                { Reject(cacheFailure); continue; }
                // 单入口前缀的中间块失去入口，由共同图改写删除；续点保留原来的定义与入边身份。
                if (edit.Replacements.Any(p => batch.Replacements.TryGetValue(p.Key, out var previous) && previous != p.Value)) continue;
                foreach (var (id, block) in edit.Blocks)
                    if (!ReferenceEquals(block, originalBlocks[id])) batch.Blocks[id] = block;
                foreach (var (from, to) in edit.Replacements) batch.Replacements[from] = to;
                assumed = candidateAssumed;
                occupied.UnionWith(region);
                if (cache) occupied.UnionWith(input.Blocks.Select(b => b.Identity));
                rejected.Remove(read.Identity);
                records.Add(new("init-guard", read.Trace?.NativeAddress, (cache ? "内部调用缓存初始化" : classFlag ? "类初始化" : methodContext ? "方法泛型上下文初始化" : "方法元数据初始化") + "模板守卫归位；" + group.Value.Evidence, true));
                changed = true;
            }
            if (!changed) break;
            input = batch.Apply();
        }
        var remaining = input.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Select(r => r.Identity).ToHashSet();
        records.AddRange(rejected.Where(p => remaining.Contains(p.Key)).Select(p => p.Value));
        retainedGuards = rejected.Where(p => remaining.Contains(p.Key) && p.Value.Reason?.Code != "structure.init-guard.generic-context")
            .Select(p => rejectedHeads[p.Key]).ToHashSet();
        finalContext = ReferenceEquals(context.Snapshot, input) ? context : names.CreateContext(input);
        return input;
    }

    /// <summary>删边后消失的使用不再计活跃；跨合流复用必须有同位置的事件后重读和非零后稳定凭据。</summary>
    private Reason? InitializationReadUses(QueryContext c, SnapshotRewrite edit, MemoryRead read, FieldName? field, InitializationGroup group)
    {
        // 用共同图改写得到精确的保留块与入边，不另建可达性遍历，也不把预览的单输入替换并入批次。
        var preview = new SnapshotRewrite(c.Snapshot);
        foreach (var (id, block) in edit.Blocks) preview.Blocks[id] = block;
        // 用途只能因删边、删块消失；不借助调用结果精化消去其他使用。
        var kept = preview.Apply();
        var after = names.CreateContext(kept);
        var index = after.Get(state.Index, 0);
        if (!index.IsSuccess) return new("structure.init-guard.read-used", "无法确定删边后守卫读取的使用。", index.Why);
        var reads = c.Get(state.Index, 0);
        if (!reads.IsSuccess) return new("structure.init-guard.read-used", "无法定位事件后的重读。", reads.Why);
        foreach (var block in c.Snapshot.Blocks.Where(b => index.Value.Blocks.ContainsKey(b.Identity)))
        foreach (var merge in block.Merges)
        {
            var predecessors = index.Value.Predecessors[block.Identity].Select(p => p.Block).ToHashSet();
            var discarded = merge.Inputs.Where(i => !predecessors.Contains(i.Predecessor)
                && SnapshotRewrite.Dependencies([i.Value]).Contains(read.Result)).ToArray();
            if (discarded.Length == 0) continue;
            Reason No(string detail) => new("structure.init-guard.read-used", $"合流（块序号 {c.Snapshot.Blocks.IndexOf(block)}，合流序号 {block.Merges.IndexOf(merge)}）的守卫读取复用凭据不足：{detail}。");
            if (discarded.Any(i => i.Value != read.Result)) return No("被删除的输入不是完整守卫读取");
            if (group.WrittenResult is null && (field is null || names.Spec.Layout.Field(field.Record, field.Field[(field.Record.Length + 1)..]).StableAfterNonzeroEvidence is not { Length: > 0 }))
                return No("位置未登记非零后稳定性");
            foreach (var incoming in merge.Inputs.Where(i => predecessors.Contains(i.Predecessor)))
            {
                if (group.WrittenResult is { } initialized && incoming.Value == initialized) continue;
                if (incoming.Value.Identity is not ResultAtom { Definition: ReadIdentity id }
                    || !reads.Value.Reads.TryGetValue(id, out var reread) || reread.Read.Width != read.Width)
                    return No("保留的输入不是同宽重读");
                if (reread.Point != group.After && c.Get(flow.PointDominates, new(group.After, reread.Point)) is not { IsSuccess: true, Value: true })
                    return No("重读不在初始化事件组之后");
                var address = c.Get(state.Resolve, read.Address);
                var again = c.Get(state.Resolve, reread.Read.Address);
                var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, read.Width)) : default;
                var other = again.IsSuccess ? c.Get(state.Locations, new(again.Value, read.Width)) : default;
                if (!location.IsSuccess || !other.IsSuccess || location.Value != other.Value
                    && (location.Value.UnknownOffsetAddress is not null || other.Value.UnknownOffsetAddress is not null
                        || (location.Value with { Root = other.Value.Root }) != other.Value
                        || names.SameValue(c, location.Value.Root, other.Value.Root) is not { IsSuccess: true, Value: true }))
                    return No("重读位置与守卫位置不相同");
            }
        }
        var uses = new SemanticUses(after, calls, state, names.Binder, names.Entry);
        return uses.Of(read.Identity).Any() ? new("structure.init-guard.read-used", "删边后守卫读取仍有真实使用。") : null;
    }

    private static readonly HashSet<string> InitializationStateFields = Cpp2CS.Runtime.RuntimeOperations.All.Values
        .SelectMany(InitializationPrefixQuery.Representations)
        .Select(r => r.Record + "." + r.Field).ToHashSet();

    private HashSet<int> InitializationStateWidths { get; } = InitializationStateFields.Select(path => path.Split('.'))
        .Select(path => checked((int)names.Spec.Layout.Field(path[0], path[1]).Size * 8)).ToHashSet();

    private static Reason? Chain(IEnumerable<Reason> reasons)
    {
        Reason? result = null;
        foreach (var reason in reasons.Reverse()) result = Append(reason, result);
        return result;
    }
    private static Reason Append(Reason reason, Reason? tail) => reason with { Cause = reason.Cause is null ? tail : Append(reason.Cause, tail) };
}
