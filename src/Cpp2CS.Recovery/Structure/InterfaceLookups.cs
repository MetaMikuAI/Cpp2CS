using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    public const string InterfaceLookupAssumption = "接口偏移表的查找循环终止（运行时不变式：表长有界）";
    private readonly InterfaceDataQuery interfaceData = new(state, calls, names, names.Spec);
    private readonly StridedAddressQuery lookupAddresses = new(state);
    private readonly IncomingValuesQuery lookupIncoming = new(state);
    private readonly FlowQueries lookupFlow = new(includeUnwind: false);

    private bool PrivateInterfaceRead(QueryContext c, MemoryRead read, BlockIdentity block)
    {
        var header = names.Spec.Layout.Field("Il2CppObject", "klass");
        if (read.Width == header.Size * 8 && header.ImmutableEvidence is { Length: > 0 }
            && c.Get(names, read.Result) is { IsSuccess: true, Value.Name: FieldName field } && field.Field == header.Path) return true;
        bool Private(Term raw)
        {
            if (PrivateAddress(c, raw, read.Width)) return true;
            // 步进视图保留实际表项身份；这里只证明字段所在的运行时私有区域。
            var address = c.Get(state.Resolve, raw);
            if (!address.IsSuccess) return false;
            var pair = names.Spec.Layout.Record("Il2CppRuntimeInterfaceOffsetPair");
            var origin = c.Get(lookupAddresses, new(address.Value, pair.Size));
            if (!origin.IsSuccess || c.Get(names, origin.Value.Base) is not
                { IsSuccess: true, Value.Kind: ValueKind.RuntimePointer, Value.Record: "Il2CppRuntimeInterfaceOffsetPair" }) return false;
            return PrivateLocation(c, new(Region.Other, origin.Value.Base, origin.Value.Remainder, read.Width));
        }
        if (Private(read.Address)) return true;
        var incoming = c.Get(lookupIncoming, new(read.Address, block));
        return incoming.IsSuccess && !incoming.Value.IsEmpty && incoming.Value.All(i => Private(i.Value));
    }

    private bool FoldInterfaceLookup(QueryContext c, SnapshotRewrite batch, HashSet<BlockIdentity> occupied,
        IReadOnlyDictionary<BlockIdentity, HashSet<BlockIdentity>> predecessors,
        List<StructureRecord> records, Dictionary<MergeIdentity, StructureRecord> rejected,
        Dictionary<ReadIdentity, StructureRecord> rejectedReads, StructureLiveness liveness, ref bool assumed)
    {
        var function = c.Snapshot;
        var countField = names.Spec.Layout.Field("Il2CppClass", "interface_offsets_count");
        var countReads = function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>()
            .Where(read => read.Width == countField.Size * 8 && c.Get(names, read.Result) is
                { IsSuccess: true, Value.Name: FieldName field } && field.Field == countField.Path).ToArray();
        void Diagnose(string code, string message, Reason? cause = null)
        {
            foreach (var read in countReads)
                rejectedReads[read.Identity] = new("interface-lookup", read.Trace?.NativeAddress, message, false)
                { Reason = new("structure.interface-lookup." + code, message, cause), Use = read.Identity };
        }
        if (!function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(call =>
            c.Get(calls, call.Identity) is { IsSuccess: true, Value.Operation.Result.Kind: RuntimeValueKind.InvokeData }))
        { Diagnose("slow-path", "候选：函数内没有已登记为接口调用数据的慢路径调用。"); return false; }
        var graph = c.Get(flow.Graph, 0);
        if (!graph.IsSuccess) { Diagnose("graph", "入口：控制流查询失败。", graph.Why); return false; }
        var normal = c.Get(lookupFlow.Graph, 0);
        if (!normal.IsSuccess) { Diagnose("graph", "入口：正常控制流查询失败。", normal.Why); return false; }
        var dataFailures = new List<Reason>();
        var regionFailures = new List<Reason>();
        Dominance? dominance = null;
        bool Dominates(BlockIdentity a, BlockIdentity b) => graph.Value.Reachable.Contains(a) && graph.Value.Reachable.Contains(b)
            && (a == b || (dominance ??= new(function)).StrictlyDominates(a, 0, b, 0));
        var heads = new Dictionary<BlockIdentity, Block?>();
        int candidates = 0;
        bool changed = false;
        foreach (var join in function.Blocks)
        foreach (var merge in join.Merges)
        {
            if (merge.Inputs.Length < 2 || occupied.Contains(join.Identity)) continue;
            var named = c.Get(interfaceData, new(merge.Result, new(join.Identity, 0)));
            if (!named.IsSuccess) { if (named.Why is { } why) dataFailures.Add(why); continue; }
            candidates++;
            void Reject(string code, string reason, Reason? cause = null)
            {
                var why = new Reason("structure.interface-lookup." + code, reason, cause);
                regionFailures.Add(why);
                rejected[merge.Identity] = new("interface-lookup", join.Trace?.NativeAddress, reason, false) { Reason = why };
            }
            var interfaceName = c.Get(names, named.Value.Interface);
            if (!interfaceName.IsSuccess || interfaceName.Value.Name is not EntityName
                { Entity: ClassEntity { Type: Cpp2CS.Model.DefinitionRef { Definition.IsInterface: true } } })
            { Reject("interface-name", "输入：接口不是已命名的接口实体。", interfaceName.Why); continue; }
            if (!heads.TryGetValue(join.Identity, out var head))
            {
                foreach (var candidate in function.Blocks)
                    if (candidate.Identity != join.Identity && Dominates(candidate.Identity, join.Identity)
                        && (head is null || Dominates(head.Identity, candidate.Identity))) head = candidate;
                heads[join.Identity] = head;
            }
            if (head is null) { Reject("entry", "入口：汇合块没有直接支配块"); continue; }
            // 前向与反向可达闭包的交集给出查找区域，允许循环。
            var forward = new HashSet<BlockIdentity>(); var pending = new Stack<BlockIdentity>(SnapshotRewrite.Targets(head.End));
            while (pending.TryPop(out var id))
                if (id != join.Identity && forward.Add(id))
                    foreach (var next in normal.Value.Successors[id]) pending.Push(next);
            var backward = new HashSet<BlockIdentity>(); pending.Push(join.Identity);
            while (pending.TryPop(out var id))
                if (backward.Add(id)) foreach (var previous in predecessors[id]) pending.Push(previous);
            var inside = forward.Intersect(backward).Where(id => id != head.Identity && id != join.Identity).ToHashSet();
            if (occupied.Contains(head.Identity) || inside.Overlaps(occupied)) continue;
            var region = function.Blocks.Where(b => inside.Contains(b.Identity)).ToArray();
            if (inside.Count == 0 || SnapshotRewrite.Targets(head.End).Any(id => !inside.Contains(id) && id != join.Identity)
                || region.Any(b => predecessors[b.Identity].Any(id => !inside.Contains(id) && id != head.Identity)))
            { Reject("boundary.entry", "边界：区域不是单入口"); continue; }
            if (region.Any(b => b.End is not (Jump or Branch) || normal.Value.Successors[b.Identity].Any(id => !inside.Contains(id) && id != join.Identity)))
            { Reject("boundary.exit", "边界：区域不是单出口"); continue; }
            if (region.Any(b => b.Handler is not null)) { Reject("handler", "异常：区域含异常处理入口"); continue; }
            var regionCalls = region.SelectMany(b => b.Statements).OfType<Call>().ToArray();
            if (regionCalls.Length != 1) { Reject("calls", "调用：区域不恰含一次查找调用"); continue; }
            var call = regionCalls[0];
            if (call.Unwind is { } target && (inside.Contains(target) || target == head.Identity || target == join.Identity))
            { Reject("unwind-region", "异常：展开目标与正常查找区域重叠。"); continue; }
            if (call.Unwind is not null && head.Statements.OfType<Call>().Any(previous => previous.Unwind is not null))
            { Reject("unwind-head", "异常：入口已有展开调用，不能合并不同调用点的展开状态。"); continue; }
            var classified = c.Get(calls, call.Identity);
            if (!classified.IsSuccess || classified.Value.Kind != CallKind.Runtime || classified.Value.Operation is not
                { Result.Kind: RuntimeValueKind.InvokeData, DoesNotReturn: false } || call.DoesNotReturn
                || classified.Value.Result?.Source is not TermSource result)
            { Reject("call-kind", "调用：唯一调用不是返回接口调用数据的运行时操作"); continue; }
            var lookup = c.Get(interfaceData, new(result.Term, new(join.Identity, 0)));
            if (!lookup.IsSuccess || !interfaceData.Same(c, named.Value, lookup.Value))
            { Reject("result", "结果：未证明查找调用与合流属于同一接口调用数据"); continue; }
            bool Frame(Term address, int width)
            {
                var resolved = c.Get(state.Resolve, address);
                return resolved.IsSuccess && c.Get(state.Locations, new(resolved.Value, width)) is { IsSuccess: true, Value.Region: Region.Frame };
            }
            var effect = region.SelectMany(b => b.Statements.Select(s => (Block: b, Statement: s))).FirstOrDefault(p => p.Statement switch
                {
                    MemoryRead r => !Frame(r.Address, r.Width) && !PrivateInterfaceRead(c, r, p.Block.Identity),
                    MemoryWrite w => !Frame(w.Address, w.Width),
                    Call => false,
                    _ => true
                });
            if (effect.Statement is MemoryRead unsupportedRead)
            {
                var reading = c.Get(names, unsupportedRead.Result);
                Reject("effects.read", $"效果：区域读取未证明为帧或运行时私有读取（{unsupportedRead.Width} 位）。",
                    reading.IsSuccess ? reading.Value.Why : reading.Why);
                continue;
            }
            if (effect.Statement is MemoryWrite) { Reject("effects.write", "效果：区域含非帧写入。"); continue; }
            if (effect.Statement is not null) { Reject("effects.statement", "效果：区域含查找以外的语句。"); continue; }
            // 帧存储也是区域定义；有外部读取或地址逃逸时不能随区域删除。
            bool StoredOutside(MemoryWrite write)
            {
                var address = c.Get(state.Resolve, write.Address);
                var location = c.Get(state.Locations, new(address.Value, write.Width));
                var escapes = c.Get(state.Escapes, 0);
                if (!location.IsSuccess || !escapes.IsSuccess || escapes.Value.MayReach(location.Value)) return true;
                foreach (var read in function.Blocks.Where(b => !inside.Contains(b.Identity)).SelectMany(b => b.Statements).OfType<MemoryRead>())
                {
                    var readAddress = c.Get(state.Resolve, read.Address);
                    if (!readAddress.IsSuccess) return true;
                    var other = c.Get(state.Locations, new(readAddress.Value, read.Width));
                    if (!other.IsSuccess || c.Get(state.Alias, new(location.Value, other.Value)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint }) return true;
                }
                return false;
            }
            if (region.SelectMany(b => b.Statements).OfType<MemoryWrite>().Any(StoredOutside))
            { Reject("frame-live", "活跃性：区域帧写入仍可能被外部读取"); continue; }

            // 将解析后的输入重新落回原生定义；不让状态查询原子进入改写后的快照。
            var available = new Dictionary<Term, Term>();
            void Available(Term value)
            {
                var resolved = c.Get(state.Resolve, value);
                if (resolved.IsSuccess) available.TryAdd(resolved.Value, value);
            }
            foreach (var block in function.Blocks.Where(b => !inside.Contains(b.Identity) &&
                Dominates(b.Identity, head.Identity)))
            {
                foreach (var m in block.Merges) Available(m.Result);
                foreach (var statement in block.Statements)
                {
                    if (statement is MemoryRead read) Available(read.Result);
                    if (statement is Call previous) foreach (var output in previous.Results) Available(output.Value);
                }
            }
            var entityReads = new Dictionary<Term, MemoryRead>();
            foreach (var read in region.SelectMany(b => b.Statements).OfType<MemoryRead>())
            {
                var resolved = c.Get(state.Resolve, read.Result);
                if (resolved.IsSuccess && PrivateAddress(c, read.Address, read.Width)
                    && c.Get(names, read.Result) is { IsSuccess: true, Value.Name: EntityName }) entityReads.TryAdd(resolved.Value, read);
            }
            var moved = new List<MemoryRead>(); var active = new HashSet<Term>();
            Term? Materialize(Term raw)
            {
                var resolved = c.Get(state.Resolve, raw);
                if (!resolved.IsSuccess) return null;
                var value = resolved.Value;
                if (available.TryGetValue(value, out var native)) return native;
                if (!active.Add(value)) return null;
                Term? answer;
                if (entityReads.TryGetValue(value, out var read))
                {
                    var address = Materialize(read.Address);
                    answer = address is null ? null : read.Result;
                    if (address is not null) { moved.Add(read with { Address = address }); available[value] = read.Result; }
                }
                else if (value.Operands.IsEmpty)
                    answer = value.Kind is TermKind.Constant or TermKind.Undefined || value.Identity is EntryAtom or RootAtom ? value : null;
                else
                {
                    var operands = value.Operands.Select(Materialize).ToArray();
                    answer = operands.Any(t => t is null) ? null : SnapshotRewrite.Rebuild(value, t => operands[value.Operands.IndexOf(t)]!);
                }
                active.Remove(value); return answer;
            }
            if (classified.Value.Inputs is not { Count: 3 } inputs || inputs.Values.Any(v => v.Source is not TermSource source || Materialize(source.Term) is null))
            { Reject("inputs", "输入：查找输入依赖区域内的非实体定义或未绑定"); continue; }
            var arguments = call.Arguments.Select(a => (Argument: a, Value: Materialize(a.Value))).ToArray();
            var area = call.OutgoingArgumentArea is { } outgoing ? Materialize(outgoing) : null;
            if (arguments.Any(a => a.Value is null) || call.OutgoingArgumentArea is not null && area is null || call.Target is ComputedTarget)
            { Reject("native-inputs", "输入：调用的原生输入不能在区域入口重建"); continue; }
            var movedCall = call with { Arguments = arguments.Select(a => a.Argument with { Value = a.Value! }).ToImmutableArray(), OutgoingArgumentArea = area };
            var external = new StructureLiveness(liveness, new HashSet<Term> { merge.Result });
            var live = new StructureLiveness(liveness, new HashSet<Term> { merge.Result }, head.Identity,
                moved.SelectMany(SnapshotRewrite.Uses).Concat(SnapshotRewrite.Uses(movedCall)));
            bool Live(Term value) => live.Outside(value, inside, head.Identity);
            var chosen = new Dictionary<Term, Term>();
            foreach (var m in function.Blocks.SelectMany(b => b.Merges).Where(m => m != merge && !Live(m.Result)))
                chosen[m.Result] = function.Terms.Undefined(m.Result.Width);
            Term Map(Term t) => chosen.TryGetValue(t, out var value) ? value : SnapshotRewrite.Rebuild(t, Map);
            bool usesUndefined = false;
            Term? Combine(Merge m, IEnumerable<Incoming> incoming)
            {
                var values = incoming.Select(i => Map(i.Value)).Distinct().ToArray();
                var defined = values.Where(t => t.Kind != TermKind.Undefined).ToArray();
                if (values.Length == 1) return values[0];
                if (defined.Length == 1) { usesUndefined = true; return defined[0]; }
                return !Live(m.Result) ? function.Terms.Undefined(m.Result.Width) : null;
            }
            bool valid = true;
            foreach (var m in region.SelectMany(b => b.Merges).Where(m => !chosen.ContainsKey(m.Result)))
            {
                var combined = Combine(m, m.Inputs);
                if (combined is null) { valid = false; break; }
                chosen[m.Result] = combined;
            }
            var merges = ImmutableArray.CreateBuilder<Merge>();
            foreach (var m in join.Merges)
            {
                var affected = m.Inputs.Where(i => inside.Contains(i.Predecessor) || i.Predecessor == head.Identity).ToArray();
                var value = m == merge ? result.Term : Combine(m, affected);
                if (value is null) { valid = false; break; }
                merges.Add(m with { Inputs = m.Inputs.Except(affected).Append(new Incoming(head.Identity, value)).ToImmutableArray() });
            }
            if (!valid) { Reject("merge-live", "合流：出口值不同且仍有使用"); continue; }
            if (region.SelectMany(b => b.Merges).Select(m => m.Result).Concat(region.SelectMany(b => b.Statements).SelectMany(s => s switch
                { MemoryRead r => new[] { r.Result }, Call x => x.Results.Select(r => r.Value), _ => [] })
                ).Any(value => external.Outside(value, inside, head.Identity)))
            { Reject("definition-live", "活跃性：区域定义仍有不经接口数据合流的外部使用"); continue; }
            Block? handler = null;
            if (call.Unwind is { } unwind)
            {
                var source = region.Single(b => b.Statements.Contains(call)).Identity;
                handler = batch.Blocks[unwind];
                var unwindMerges = ImmutableArray.CreateBuilder<Merge>();
                foreach (var m in handler.Merges)
                {
                    var incoming = ImmutableArray.CreateBuilder<Incoming>();
                    foreach (var input in m.Inputs)
                    {
                        if (input.Predecessor != source) { incoming.Add(input); continue; }
                        var value = Materialize(Map(input.Value));
                        if (value is null || m.Inputs.Any(other => other.Predecessor == head.Identity)) { valid = false; break; }
                        incoming.Add(new(head.Identity, value));
                    }
                    if (!valid) break;
                    unwindMerges.Add(m with { Inputs = incoming.ToImmutable() });
                }
                if (!valid) { Reject("unwind-inputs", "异常：展开边的活跃状态不能在区域入口重建。"); continue; }
                handler = handler with { Merges = unwindMerges.ToImmutable() };
            }
            foreach (var (from, to) in chosen) batch.Replacements[from] = to;
            batch.Blocks[join.Identity] = join with { Merges = merges.ToImmutable() };
            batch.Blocks[head.Identity] = head with { Statements = head.Statements.AddRange(moved).Add(movedCall), End = new Jump(join.Identity) };
            batch.RemovedBlocks.UnionWith(inside);
            occupied.UnionWith(inside); occupied.Add(head.Identity); occupied.Add(join.Identity);
            if (handler is not null) { batch.Blocks[handler.Identity] = handler; occupied.Add(handler.Identity); }
            assumed |= usesUndefined;
            rejected.Remove(merge.Identity);
            records.Add(new("interface-lookup", join.Trace?.NativeAddress, "同一接口调用数据的快慢路径折叠为入口处的一次查找", true));
            changed = true;
        }
        var failure = regionFailures.FirstOrDefault() ?? dataFailures.FirstOrDefault(r => r.Code != "dispatch.interface-source");
        if (failure is not null) Diagnose(candidates == 0 ? "data" : "region",
            candidates == 0 ? "候选：没有合流被证明为同一接口调用数据。" : "区域：已命名的接口调用数据未通过区域折叠。", failure);
        else Diagnose("candidate", "候选：没有可折叠的调用数据地址合流；字段合流尚未作为区域出口查询。");
        return changed;
    }
}
