using System.Collections.Immutable;
using System.Diagnostics;
using System.Reflection;
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

namespace Cpp2CS.Recovery.Structure;

public sealed record StructureRecord(string Kind, ulong? Address, string Evidence, bool Removed);
public sealed record StructureResult(NativeFunction Function, ImmutableArray<StructureRecord> Records,
    ImmutableArray<string> Assumptions)
{
    public ImmutableDictionary<string, double> Timings { get; init; } = ImmutableDictionary<string, double>.Empty;
    /// <summary>变换所依据的命名事实；下降沿用它给变换后留下的槽位读取命名。</summary>
    public NamingFacts Names { get; init; } = NamingFacts.Empty;
}

/// <summary>按私有状态和运行时登记消去效果；每次改图后重新建立查询上下文。</summary>
public sealed partial class UnobservableEffects(StateQueries state, CallNamingQuery calls, ValueNamingQuery names,
    IImage image, IReadOnlySet<AbstractSlot>? returnSlots = null,
    Cpp2CS.Recovery.Locations.ManagedLocationQuery? locations = null, ClassInitializationQuery? initialization = null)
{
    public const string UndefinedAssumption = "生成代码的可观察行为不依赖未定义的值。";
    private readonly FlowQueries flow = new();

    public StructureResult Run(NativeFunction input)
    {
        var timer = Stopwatch.StartNew();
        var timings = new Dictionary<string, double>();
        double regionTime = 0, liveTime = 0, rewriteTime = 0;
        var records = new List<StructureRecord>(); bool assumed = false;
        var original = input;
        input = ReplaceSpecificationResults(input, records, out var c);
        if (!ReferenceEquals(input, original)) c = names.CreateContext(input);
        var edit = new SnapshotRewrite(input);
        var erased = new Dictionary<Statement, StructureRecord>();
        var classRecords = new Dictionary<CallIdentity, StructureRecord>();
        foreach (var b in input.Blocks)
        foreach (var s in b.Statements)
        {
            string? evidence = null;
            if (s is MemoryWrite w && PrivateAddress(c, w.Address, w.Width)) evidence = "运行时私有状态写入";
            if (s is Call call)
            {
                var named = c.Get(calls, call.Identity);
                if (named.IsSuccess && named.Value.Kind == CallKind.Runtime && named.Value.Operation is { } op)
                {
                    if (call.DoesNotReturn || op.DoesNotReturn)
                    {
                        if (op.Observation != RuntimeObservation.Observable)
                            records.Add(new("termination", s.Trace?.NativeAddress, "调用含不返回结局", false));
                        continue;
                    }
                    if (op.RelaxedClassInput is { } classInput)
                    {
                        var relaxed = RelaxedClass(c, named.Value, classInput);
                        if (relaxed.Allowed == true) evidence = relaxed.Evidence;
                        else
                        {
                            var record = new StructureRecord(relaxed.Allowed == false ? "precise-class-init" : "class-unknown",
                                s.Trace?.NativeAddress, relaxed.Evidence, false);
                            records.Add(record); classRecords[call.Identity] = record;
                        }
                    }
                    else if (names.DefinitionMethod is not null && op.MetadataInitialization is { } metadata
                        && named.Value.Inputs?.GetValueOrDefault(metadata.Input)?.Source is TermSource source
                        && c.Get(names, source.Term) is { IsSuccess: true } target && names.ContextEntity(target.Value.Name))
                        evidence = metadata.Evidence;
                    else if (op.Observation == RuntimeObservation.Unobservable)
                        evidence = op.Name;
                }
            }
            if (evidence is null) continue;
            edit.RemovedStatements.Add(s);
            if (s is Call removed) foreach (var r in removed.Results) edit.Replacements[r.Value] = input.Terms.Undefined(r.Value.Width);
            erased[s] = new(s is Call ? "call" : "private-write", s.Trace?.NativeAddress, evidence, true);
        }
        timings["候选消去"] = timer.Elapsed.TotalSeconds;
        // 不可观察只描述效果；有定义的实际返回值仍不能冒充 ABI 未定义位。
        var liveResults = SnapshotRewrite.Dependencies(input.Blocks.SelectMany(b =>
            b.Statements.Where(s => !edit.RemovedStatements.Contains(s)).SelectMany(SnapshotRewrite.Uses).Concat(EndUses(b.End))));
        bool added;
        do
        {
            int count = liveResults.Count;
            foreach (var m in input.Blocks.SelectMany(b => b.Merges).Where(m => liveResults.Contains(m.Result)))
                liveResults.UnionWith(SnapshotRewrite.Dependencies(m.Inputs.Select(i => i.Value)));
            foreach (var call in edit.RemovedStatements.OfType<Call>().ToArray())
            {
                var classified = c.Get(calls, call.Identity).Value;
                var bound = classified.Result?.Source;
                var defined = bound is TermSource value ? SnapshotRewrite.Dependencies([value.Term])
                    : classified.Function?.Signature?.ReturnType.Size == 0 ? []
                    : call.Results.Select(r => r.Value).ToHashSet();
                if (!call.Results.Any(r => defined.Contains(r.Value) && liveResults.Contains(r.Value))) continue;
                edit.RemovedStatements.Remove(call);
                foreach (var result in call.Results) edit.Replacements.Remove(result.Value);
                erased.Remove(call);
                records.Add(new("runtime-result-used", call.Trace?.NativeAddress, classified.Operation!.Name + " 的实际返回值仍有使用", false));
                liveResults.UnionWith(SnapshotRewrite.Dependencies(SnapshotRewrite.Uses(call)));
            }
            added = count != liveResults.Count;
        } while (added);
        records.AddRange(erased.Values);
        timings["结果活跃性"] = timer.Elapsed.TotalSeconds - timings["候选消去"];
        var rewriteInitial = timer.Elapsed.TotalSeconds;
        var erasedSnapshot = edit.RemovedStatements.Count == 0 ? input : edit.Apply();
        timings["初始改写"] = timer.Elapsed.TotalSeconds - rewriteInitial;
        var forwardInitial = timer.Elapsed.TotalSeconds;
        var current = edit.RemovedStatements.Count == 0 ? input : ForwardReads(erasedSnapshot, records);
        // 调用只读取签名绑定的输入槽；先裁掉其余的槽，折叠时的活跃性才不被它们牵住。
        current = RemoveUnusedCallInputs(current, records);
        timings["读取转发"] = timer.Elapsed.TotalSeconds - forwardInitial;
        // 未绑定的返回槽没有托管使用；只有发生结构改写时才裁剪它们。
        timings["消去与读取转发"] = timer.Elapsed.TotalSeconds;
        var rejected = new Dictionary<BlockIdentity, StructureRecord>();
        var rejectedLookups = new Dictionary<MergeIdentity, StructureRecord>();
        bool foldedLookup = false;
        var retainedInitializations = new Dictionary<CallIdentity, StructureRecord>();
        while (true)
        {
            var foldStart = timer.Elapsed.TotalSeconds;
            while (true)
            {
                c = names.CreateContext(current);
                bool changed = false;
                var byId = current.Blocks.ToDictionary(b => b.Identity);
                var allMerges = current.Blocks.SelectMany(b => b.Merges).ToArray();
                var regionQuery = new SnapshotRegionQuery(flow);
                var predecessors = current.Blocks.ToDictionary(b => b.Identity, _ => new HashSet<BlockIdentity>());
                foreach (var block in current.Blocks)
                    foreach (var target in SnapshotRewrite.Targets(block.End).Concat(block.Statements.OfType<Call>().Where(call => call.Unwind is not null).Select(call => call.Unwind!)))
                        predecessors[target].Add(block.Identity);
                var batch = new SnapshotRewrite(current);
                var occupied = new HashSet<BlockIdentity>();
                var liveStart = timer.Elapsed.TotalSeconds;
                var liveness = new StructureLiveness(current, EndUses);
                liveTime += timer.Elapsed.TotalSeconds - liveStart;
                changed = FoldInterfaceLookup(c, batch, occupied, predecessors, records, rejectedLookups, ref assumed);
                foldedLookup |= changed;
                foreach (var b in current.Blocks.Where(b => b.End is Branch))
                {
                    var branch = (Branch)b.End;
                    if (!PrivateCondition(c, branch.Condition))
                    { rejected[b.Identity] = new("condition", b.Trace?.NativeAddress, "条件不只依赖常量和运行时私有状态", false); continue; }
                    var graph = c.Get(flow.Graph, 0);
                    if (!graph.IsSuccess) continue;
                    string failure = "没有可证明的汇合点";
                    var guarded = Guarded(c, b, byId, predecessors, out var guardFailure);
                    failure = guardFailure ?? failure;
                    var nearest = guarded?.Join ?? NearestJoin(c, branch, byId);
                    foreach (var join in nearest is null ? Array.Empty<Block>() : new[] { nearest })
                    {
                        var stamp = timer.Elapsed.TotalSeconds;
                        var region = guarded is null ? c.Get(regionQuery, new(b.Identity, join.Identity))
                            : Outcome<SnapshotRegion>.Success(new(guarded.Inside));
                        regionTime += timer.Elapsed.TotalSeconds - stamp;
                        if (!region.IsSuccess) continue;
                        var inside = region.Value.Order.ToHashSet();
                        var blocks = region.Value.Order.Select(id => byId[id]).ToArray();
                        if (occupied.Contains(b.Identity) || occupied.Contains(join.Identity) || inside.Overlaps(occupied)) continue;
                        if (blocks.Any(x => x.Statements.Any(s => s is not MemoryRead && s != guarded?.Event) || x.Handler is not null ||
                            x.End is not (Jump or Branch) || x.End is Branch br && !PrivateCondition(c, br.Condition)))
                        { failure = "区域仍含语句或可观察条件"; continue; }
                        var candidate = new SnapshotRewrite(current);
                        // 私有读取可以留到区域删除；其他读取必须已无使用。
                        bool Live(Term value) => liveness.Outside(value, inside, b.Identity);
                        // 不活跃合流可能仍串成使用链；一起裁剪，避免保留已删除区域的定义引用。
                        foreach (var merge in allMerges.Where(m => !Live(m.Result)))
                            candidate.Replacements[merge.Result] = current.Terms.Undefined(merge.Result.Width);
                        if (blocks.SelectMany(x => x.Statements).OfType<MemoryRead>().Any(r => Live(r.Result)))
                        { failure = "区域读取仍有外部使用"; continue; }
                        if (blocks.SelectMany(x => x.Statements).OfType<MemoryRead>().Any(r => !PrivateAddress(c, r.Address, r.Width)))
                        { failure = "区域仍含非私有读取"; continue; }
                        var chosen = new Dictionary<Term, Term>();
                        if (guarded is not null)
                            foreach (var result in guarded.Event.Results) chosen[result.Value] = current.Terms.Undefined(result.Value.Width);
                        bool valid = true, usesUndefined = false;
                        Term Map(Term t) => chosen.TryGetValue(t, out var v) ? v : SnapshotRewrite.Rebuild(t, Map);
                        Term? Combine(Merge m, IEnumerable<Incoming> inputs)
                        {
                            var values = inputs.Select(i => Map(i.Value)).Distinct().ToArray();
                            var defined = values.Where(t => t.Kind != TermKind.Undefined).ToArray();
                            if (values.Length == 1) return values[0];
                            if (defined.Length == 1) { usesUndefined = true; return defined[0]; }
                            if (!Live(m.Result)) return current.Terms.Undefined(m.Result.Width);
                            return null;
                        }
                        foreach (var id in region.Value.Order)
                            foreach (var m in byId[id].Merges)
                            {
                                var value = Combine(m, m.Inputs);
                                if (value is null) { valid = false; break; }
                                chosen[m.Result] = value;
                            }
                        if (!valid) { failure = "合流值不同且仍有使用"; continue; }
                        var merges = ImmutableArray.CreateBuilder<Merge>();
                        foreach (var m in join.Merges)
                        {
                            var affected = m.Inputs.Where(i => inside.Contains(i.Predecessor) || i.Predecessor == b.Identity).ToArray();
                            var value = Combine(m, affected);
                            if (value is null) { valid = false; break; }
                            merges.Add(m with { Inputs = m.Inputs.Except(affected).Append(new Incoming(b.Identity, value)).ToImmutableArray() });
                        }
                        if (!valid) { failure = "合流值不同且仍有使用"; continue; }
                        // 删除区域定义前，所有使用必须已被替换或随区域一起删除。
                        foreach (var (from, to) in chosen) candidate.Replacements[from] = to;
                        candidate.Blocks[join.Identity] = candidate.Blocks[join.Identity] with { Merges = merges.ToImmutable() };
                        candidate.Blocks[b.Identity] = b with { End = new Jump(join.Identity),
                            Statements = guarded is null ? b.Statements : b.Statements.Add(guarded.Event) };
                        candidate.RemovedBlocks.UnionWith(inside);
                        foreach (var (id, block) in candidate.Blocks)
                            if (!ReferenceEquals(block, byId[id])) batch.Blocks[id] = block;
                        foreach (var (from, to) in candidate.Replacements) batch.Replacements[from] = to;
                        batch.RemovedBlocks.UnionWith(inside);
                        occupied.UnionWith(inside); occupied.Add(b.Identity); occupied.Add(join.Identity);
                        foreach (var read in blocks.SelectMany(x => x.Statements).OfType<MemoryRead>())
                            records.Add(new("private-read", read.Trace?.NativeAddress, "随无效果区域删除的私有读取", true));
                        assumed |= usesUndefined;
                        records.Add(new("branch", b.Trace?.NativeAddress, guarded is null ? "条件仅依赖私有状态，区域无可观察效果，出口合流兼容"
                            : "同一状态后置条件守卫的幂等事件；" + guarded.Evidence, true));
                        rejected.Remove(b.Identity);
                        changed = true; failure = ""; break;
                    }
                    if (failure.Length == 0) continue;
                    rejected[b.Identity] = new("branch-retained", b.Trace?.NativeAddress, failure, false);
                }
                if (!changed) break;
                var rewriteStart = timer.Elapsed.TotalSeconds;
                if (returnSlots is not null)
                    foreach (var block in batch.Blocks.Values.Where(x => x.End is Return).ToArray())
                        batch.Blocks[block.Identity] = block with { End = new Return(((Return)block.End).Results.Where(r => returnSlots.Contains(r.Slot)).ToImmutableArray()) };
                current = batch.Apply();
                rewriteTime += timer.Elapsed.TotalSeconds - rewriteStart;
            }
            timings["折叠总计"] = timings.GetValueOrDefault("折叠总计") + timer.Elapsed.TotalSeconds - foldStart;
            timings["区域查询"] = regionTime; timings["活跃性"] = liveTime; timings["改写"] = rewriteTime;
            var deadStart = timer.Elapsed.TotalSeconds;
            if (!ReferenceEquals(current, input)) current = RemoveDeadPrivateReads(current, records);
            timings["死读取"] = timings.GetValueOrDefault("死读取") + timer.Elapsed.TotalSeconds - deadStart;
            var absorptionStart = timer.Elapsed.TotalSeconds;
            var beforeAbsorption = current;
            current = AbsorbClassInitialization(current, records, retainedInitializations, classRecords);
            timings["类初始化吸收"] = timings.GetValueOrDefault("类初始化吸收") + timer.Elapsed.TotalSeconds - absorptionStart;
            if (ReferenceEquals(current, beforeAbsorption)) break;
            current = RemoveUnusedCallInputs(current, records);
        }
        var remaining = current.Blocks.Select(b => b.Identity).ToHashSet();
        records.AddRange(retainedInitializations.Values);
        records.AddRange(rejected.Where(p => remaining.Contains(p.Key)).Select(p => p.Value));
        var remainingMerges = current.Blocks.SelectMany(b => b.Merges).Select(m => m.Identity).ToHashSet();
        records.AddRange(rejectedLookups.Where(p => remainingMerges.Contains(p.Key)).Select(p => p.Value));
        var assumptions = ImmutableArray.CreateBuilder<string>();
        if (assumed) assumptions.Add(UndefinedAssumption);
        if (foldedLookup) assumptions.Add(InterfaceLookupAssumption);
        return new(current, records.ToImmutableArray(), assumptions.ToImmutable()) { Timings = timings.ToImmutableDictionary() };
    }

    // 分支点位于入口块的终结之后，故忽略该块此前调用的异常出口。
    private Block? NearestJoin(QueryContext c, Branch branch, IReadOnlyDictionary<BlockIdentity, Block> blocks)
    {
        if (c.Get(flow.PostDominates, new(branch.True, branch.False)) is { IsSuccess: true, Value: true }) return blocks[branch.True];
        if (c.Get(flow.PostDominates, new(branch.False, branch.True)) is { IsSuccess: true, Value: true }) return blocks[branch.False];
        var graph = c.Get(flow.Graph, 0);
        if (!graph.IsSuccess || graph.Value.Exits.Contains(branch.True) || graph.Value.Exits.Contains(branch.False)) return null;
        Block? nearest = null;
        foreach (var candidate in blocks.Values)
        {
            if (c.Get(flow.PostDominates, new(candidate.Identity, branch.True)) is not { IsSuccess: true, Value: true }
                || c.Get(flow.PostDominates, new(candidate.Identity, branch.False)) is not { IsSuccess: true, Value: true }) continue;
            if (nearest is null || c.Get(flow.PostDominates, new(nearest.Identity, candidate.Identity)) is { IsSuccess: true, Value: true })
                nearest = candidate;
        }
        return nearest;
    }

    private NativeFunction ForwardReads(NativeFunction function, List<StructureRecord> records)
    {
        var c = names.CreateContext(function);
        var edit = new SnapshotRewrite(function);
        foreach (var read in function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>())
        {
            var value = c.Get(state.Read, read.Identity);
            if (!value.IsSuccess || value.Value == read.Result) continue;
            var terms = SnapshotRewrite.Dependencies([value.Value]);
            // 状态查询可以给出帧转发或只读映像内容；状态原子只用于查询，不进入原生快照。
            if (terms.Contains(read.Result) || terms.Any(t => t.Kind == TermKind.Atom &&
                t.Identity is not (EntryAtom or ResultAtom or RootAtom or CallerValue or ExceptionAtom or SelectorAtom))) continue;
            edit.RemovedStatements.Add(read); edit.Replacements[read.Result] = value.Value;
            records.Add(new("forwarded-read", read.Trace?.NativeAddress, "状态查询给出原生词汇内的等值项", true));
        }
        ForwardEntityReads(function, records, c, edit);
        return edit.RemovedStatements.Count == 0 ? function : edit.Apply();
    }

    private NativeFunction AbsorbClassInitialization(NativeFunction function, List<StructureRecord> records,
        Dictionary<CallIdentity, StructureRecord> retained, Dictionary<CallIdentity, StructureRecord> initialRecords)
    {
        if (locations is null || initialization is null) return function;
        var c = locations.CreateContext(function);
        var edit = new SnapshotRewrite(function);
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            var classified = c.Get(calls, call.Identity);
            if (!classified.IsSuccess || classified.Value.Operation is not
                { RelaxedClassInput: not null, Observation: RuntimeObservation.IdempotentEvent }) continue;
            if (initialRecords.Remove(call.Identity, out var previous)) records.Remove(previous);
            var result = c.Get(initialization, call.Identity);
            if (!result.IsSuccess || !result.Value.CanAbsorb)
            {
                var why = result.Why ?? result.Value.Why!;
                while (why.Cause is { } cause) why = cause;
                retained[call.Identity] = new("class-init-retained", call.Trace?.NativeAddress,
                    why.Code + "：" + why.Message, false);
                continue;
            }
            edit.RemovedStatements.Add(call);
            foreach (var value in call.Results) edit.Replacements[value.Value] = function.Terms.Undefined(value.Value.Width);
            retained.Remove(call.Identity);
            records.Add(new("class-init-absorbed", call.Trace?.NativeAddress, "每条路径的首个观察均为同类访问，隐含同一精确初始化", true));
        }
        return edit.RemovedStatements.Count == 0 ? function : edit.Apply();
    }

    private IEnumerable<Term> EndUses(Terminator end) => end is Return r && returnSlots is not null
        ? r.Results.Where(v => returnSlots.Contains(v.Slot)).Select(v => v.Value) : SnapshotRewrite.Uses(end);

    private NativeFunction RemoveDeadPrivateReads(NativeFunction f, List<StructureRecord> records)
    {
        while (true)
        {
            var c = names.CreateContext(f);
            var live = SnapshotRewrite.Dependencies(f.Blocks.SelectMany(b => b.Statements.SelectMany(SnapshotRewrite.Uses)
                .Concat(EndUses(b.End)).Concat(b.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)))));
            var edit = new SnapshotRewrite(f);
            foreach (var r in f.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>())
                if (!live.Contains(r.Result) && PrivateAddress(c, r.Address, r.Width))
                { edit.RemovedStatements.Add(r); records.Add(new("private-read", r.Trace?.NativeAddress, "私有读取没有使用", true)); }
            if (edit.RemovedStatements.Count == 0) return f;
            if (returnSlots is not null)
                foreach (var b in f.Blocks.Where(b => b.End is Return))
                    edit.Blocks[b.Identity] = b with { End = new Return(((Return)b.End).Results.Where(r => returnSlots.Contains(r.Slot)).ToImmutableArray()) };
            f = edit.Apply();
        }
    }
    private (bool? Allowed, string Evidence) RelaxedClass(QueryContext c, ClassifiedCall call, string input)
    {
        if (call.Inputs?.GetValueOrDefault(input)?.Source is not TermSource source) return (null, "类实参未绑定");
        var name = c.Get(names, source.Term);
        if (!name.IsSuccess || name.Value.Name is not EntityName { Entity: ClassEntity { Type: DefinitionRef type } }) return (null, "目标类缺少元数据凭据");
        if ((type.Definition.Attributes & TypeAttributes.BeforeFieldInit) != 0) return (true, "类元数据带 beforefieldinit");
        return !type.Definition.Methods.Any(m => m.Name == ".cctor") ? (true, "类元数据无静态构造函数")
            : (false, "显式静态构造且无 beforefieldinit");
    }
    private bool PrivateAddress(QueryContext c, Term address, int width)
    {
        var value = c.Get(state.Resolve, address); if (!value.IsSuccess) return false;
        var location = c.Get(state.Locations, new(value.Value, width));
        return location.IsSuccess && PrivateLocation(c, location.Value);
    }
    private bool PrivateLocation(QueryContext c, Location location)
    {
        if (location.Region == Region.Image && location.Offset is { } offset && offset >= 0 && offset <= ulong.MaxValue)
        {
            var info = image.Query((ulong)offset);
            return info.Storage != StorageKind.Unmapped && info.Writable && !info.Executable
                && info.AvailableBytes >= (ulong)((location.Width + 7L) / 8);
        }
        if (location.Region != Region.Other || location.Offset is null) return false;
        var owner = c.Get(names, location.Root);
        if (!owner.IsSuccess || owner.Value.Kind != ValueKind.RuntimePointer || owner.Value.Record is null) return false;
        // 指针种类不足以证明任意偏移；字段范围必须由命名查询确认。
        var named = c.Get(names, c.Snapshot.Terms.Atom(new MemoryAtom(location, null), location.Width));
        return named.IsSuccess && (named.Value.Name is FieldName or BitStorageName
            || names.DefinitionMethod is not null && named.Value.Name is EntityName);
    }
    private bool PrivateCondition(QueryContext c, Term condition)
    {
        var resolved = c.Get(state.Resolve, condition); if (!resolved.IsSuccess) return false;
        bool Check(Term t) => t.Kind == TermKind.Constant || t.Identity is MemoryAtom memory && PrivateLocation(c, memory.Location)
            || t.Kind is TermKind.Operation or TermKind.Slice or TermKind.Concat && t.Operands.All(Check);
        return Check(resolved.Value);
    }
}
