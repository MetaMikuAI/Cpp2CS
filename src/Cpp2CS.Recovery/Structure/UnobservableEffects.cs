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

public sealed record StructureRecord(string Kind, ulong? Address, string Evidence, bool Removed)
{
    /// <summary>拒绝改写的原因；接在下降失败原因链的末尾。</summary>
    public Reason? Reason { get; init; }
    /// <summary>拒绝改写的原因；作为洞的首因，下降的失败原因成为它的原因。</summary>
    public Reason? Why { get; init; }
    /// <summary>使用处消失时一并删除的诊断锚点。</summary>
    internal StableIdentity? Use { get; init; }
}
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
        var records = new List<StructureRecord>();
        var rejected = new List<StructureRecord>();
        var assumptions = new HashSet<string>();
        var timings = new Dictionary<string, double>();
        while (true)
        {
            var result = Normalize(input);
            records.AddRange(result.Records.Where(r => r.Removed));
            assumptions.UnionWith(result.Assumptions);
            foreach (var (key, seconds) in result.Timings) timings[key] = timings.GetValueOrDefault(key) + seconds;
            // 只有消去了已知实体的元数据初始化（泛型上下文、类的布局就绪），新快照才可能让原先未知的实体可命名；
            // 其余情形一遍就是最终结果，不重复。
            if (ReferenceEquals(result.Function, input) || !contextInitialization)
            {
                // 前几遍留下的拒绝原因，只要同一位置后来既没有被改写、最后一遍也没有重新给出，就保留：
                // 后面的遍可能改掉了让它被认出来的那部分代码，原因仍然是这个位置没能改写的依据。
                // 初始化调用消去后仍可能重跑；守卫的拒绝原因沿用事件尚在时的凭据。
                var last = result.Records.Where(r => !r.Removed).Select(r => r.Kind == "init-guard"
                    ? rejected.FirstOrDefault(x => x.Kind == r.Kind && x.Address == r.Address) ?? r : r).ToArray();
                var kept = rejected.Where(r => !records.Any(x => x.Kind == r.Kind && x.Address == r.Address)
                    && !last.Any(x => x.Kind == r.Kind && x.Address == r.Address)).ToArray();
                var finalRecords = records.Concat(last).Concat(kept).ToImmutableArray();
                if (finalRecords.Any(r => r.Use is not null))
                {
                    var liveUses = result.Function.Blocks.SelectMany(b => b.Statements.Select(s => SlotUseIdentity(s, b.Identity))
                        .Append(b.Identity)).ToHashSet();
                    finalRecords = finalRecords.Where(r => r.Use is null || liveUses.Contains(r.Use)).ToImmutableArray();
                }
                return result with { Records = finalRecords,
                    Assumptions = [.. assumptions.Order(StringComparer.Ordinal)], Timings = timings.ToImmutableDictionary() };
            }
            foreach (var r in result.Records.Where(r => !r.Removed && (r.Reason is not null || r.Why is not null)))
                if (!rejected.Any(x => x.Kind == r.Kind && x.Address == r.Address)) rejected.Add(r);
            // 新快照可使原先未知的元数据实体可命名；只重复同一消去过程。
            // 每次改写均减少块、调用、语句或未使用的槽，不增加原生控制流。
            input = result.Function;
        }
    }

    private bool contextInitialization;

    private StructureResult Normalize(NativeFunction input)
    {
        contextInitialization = false;
        var timer = Stopwatch.StartNew();
        var timings = new Dictionary<string, double>();
        double regionTime = 0, liveTime = 0, rewriteTime = 0;
        var records = new List<StructureRecord>(); bool assumed = false;
        var original = input;
        input = ReplaceSpecificationResults(input, records, out var c);
        if (!ReferenceEquals(input, original)) c = names.CreateContext(input);
        var guardStart = timer.Elapsed.TotalSeconds;
        input = FoldInitializationGuards(input, records, c, out var retainedGuards, out c, ref assumed);
        timings["初始化守卫"] = timer.Elapsed.TotalSeconds - guardStart;
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
                    else if (op.MetadataInitialization is { } metadata
                        && named.Value.Inputs?.GetValueOrDefault(metadata.Input)?.Source is TermSource source
                        && c.Get(names, source.Term) is { IsSuccess: true } target && names.ContextEntity(target.Value.Name))
                    { evidence = metadata.Evidence; contextInitialization = true; }
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
                var defined = DefinedCallResults(classified, call);
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
        // 先裁掉签名不读取的槽，避免无用的帧位型使逃逸与读取转发失去精度。
        var trimmed = RemoveUnusedCallInputs(erasedSnapshot, records, out var unresolvedInputs);
        var current = edit.RemovedStatements.Count == 0 ? trimmed : ForwardReads(trimmed, records);
        // 读取转发可能补出间接分派的身份；只在快照变化时补裁一次。
        if (unresolvedInputs && !ReferenceEquals(current, trimmed)) current = RemoveUnusedCallInputs(current, records);
        timings["读取转发"] = timer.Elapsed.TotalSeconds - forwardInitial;
        // 未绑定的返回槽没有托管使用；只有发生结构改写时才裁剪它们。
        timings["消去与读取转发"] = timer.Elapsed.TotalSeconds;
        var rejected = new Dictionary<BlockIdentity, StructureRecord>();
        var rejectedLookups = new Dictionary<MergeIdentity, StructureRecord>();
        var rejectedTypeChecks = new Dictionary<Term, ImmutableArray<StructureRecord>>();
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
                var typeCheckStart = timer.Elapsed.TotalSeconds;
                bool foldedTypeCheck = FoldArrayStoreCheck(c, batch, records, rejectedTypeChecks)
                    || FoldTypeCheck(c, batch, predecessors, records, rejectedTypeChecks);
                timings["类型判断"] = timings.GetValueOrDefault("类型判断") + timer.Elapsed.TotalSeconds - typeCheckStart;
                if (foldedTypeCheck)
                {
                    current = RemoveDeadPrivateReads(batch.Apply(), records);
                    continue;
                }
                var liveStart = timer.Elapsed.TotalSeconds;
                var liveness = new StructureLiveness(current, EndUses);
                liveTime += timer.Elapsed.TotalSeconds - liveStart;
                changed = FoldInterfaceLookup(c, batch, occupied, predecessors, records, rejectedLookups, ref assumed);
                foldedLookup |= changed;
                bool hasProtectionFailure = current.Blocks.SelectMany(x => x.Statements).OfType<Call>().Any(call =>
                    c.Get(calls, call.Identity) is { IsSuccess: true, Value.Operation.Name: "StackProtectionFailure" });
                foreach (var b in current.Blocks.Where(b => b.End is Branch))
                {
                    if (retainedGuards.Contains(b.Identity)) continue;
                    var branch = (Branch)b.End;
                    if (hasProtectionFailure && FoldStackProtection(c, batch, b, records))
                    { occupied.Add(b.Identity); changed = true; continue; }
                    if (!PrivateCondition(c, branch.Condition))
                    { rejected[b.Identity] = new("condition", b.Trace?.NativeAddress, "条件不只依赖常量和运行时私有状态", false); continue; }
                    var graph = c.Get(flow.Graph, 0);
                    if (!graph.IsSuccess) continue;
                    string failure = "没有可证明的汇合点";
                    var nearest = NearestJoin(c, branch, byId);
                    foreach (var join in nearest is null ? Array.Empty<Block>() : new[] { nearest })
                    {
                        var stamp = timer.Elapsed.TotalSeconds;
                        var region = c.Get(regionQuery, new(b.Identity, join.Identity));
                        regionTime += timer.Elapsed.TotalSeconds - stamp;
                        if (!region.IsSuccess) continue;
                        var inside = region.Value.Order.ToHashSet();
                        var blocks = region.Value.Order.Select(id => byId[id]).ToArray();
                        if (occupied.Contains(b.Identity) || occupied.Contains(join.Identity) || inside.Overlaps(occupied)) continue;
                        if (blocks.Any(x => x.Statements.Any(s => s is not MemoryRead) || x.Handler is not null ||
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
                        bool valid = true, usesUndefined = false;
                        Term Map(Term t) => chosen.TryGetValue(t, out var v) ? v : SnapshotRewrite.Rebuild(t, Map);
                        Term? Combine(Merge m, IEnumerable<Incoming> inputs)
                        {
                            var value = MergeValue(inputs.Select(i => Map(i.Value)), out var refined);
                            if (value is not null) { usesUndefined |= refined; return value; }
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
                            Statements = b.Statements };
                        candidate.RemovedBlocks.UnionWith(inside);
                        foreach (var (id, block) in candidate.Blocks)
                            if (!ReferenceEquals(block, byId[id])) batch.Blocks[id] = block;
                        foreach (var (from, to) in candidate.Replacements) batch.Replacements[from] = to;
                        batch.RemovedBlocks.UnionWith(inside);
                        occupied.UnionWith(inside); occupied.Add(b.Identity); occupied.Add(join.Identity);
                        foreach (var read in blocks.SelectMany(x => x.Statements).OfType<MemoryRead>())
                            records.Add(new("private-read", read.Trace?.NativeAddress, "随无效果区域删除的私有读取", true));
                        assumed |= usesUndefined;
                        records.Add(new("branch", b.Trace?.NativeAddress, "条件仅依赖私有状态，区域无可观察效果，出口合流兼容", true));
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
            if (!ReferenceEquals(current, input) || !ReferenceEquals(input, original)) current = RemoveDeadPrivateReads(current, records);
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
        var remainingTerms = SnapshotRewrite.Dependencies(current.Blocks.SelectMany(b => b.Statements.SelectMany(SnapshotRewrite.Uses)
            .Concat(EndUses(b.End)).Concat(b.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)))));
        records.AddRange(rejectedTypeChecks.Where(p => remainingTerms.Contains(p.Key)).SelectMany(p => p.Value));
        var assumptions = ImmutableArray.CreateBuilder<string>();
        if (assumed || records.Any(r => r.Kind == "unbox-fusion-undefined")) assumptions.Add(UndefinedAssumption);
        if (records.Any(r => r.Kind == "stack-protection" && r.Removed)) assumptions.Add(StackProtectionAssumption);
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
        ForwardFixedReads(function, records, c, edit);
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
                    why.Code + "：" + why.Message, false) { Reason = why };
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
            || named.Value.Name is EntityName);
    }
    private bool PrivateCondition(QueryContext c, Term condition)
    {
        var resolved = c.Get(state.Resolve, condition); if (!resolved.IsSuccess) return false;
        var active = new HashSet<Term>();
        bool Check(Term t)
        {
            var value = c.Get(state.Resolve, t); if (!value.IsSuccess) return false;
            t = value.Value;
            if (!active.Add(t)) return false;
            // 合流和选择按私有内容的来源判定；选择条件仍保留在值选择中。
            bool result = t.Kind == TermKind.Constant || t.Identity is MemoryAtom memory && PrivateLocation(c, memory.Location)
                || t.Operator is CoreOperator { Operation: CoreOperation.Select } && !t.Operands[0].ContainsUndefined && t.Operands.Skip(1).All(Check)
                || t.Operator is not CoreOperator { Operation: CoreOperation.Select }
                    && (t.Kind is TermKind.Operation or TermKind.Slice or TermKind.Concat) && t.Operands.All(Check)
                || t.Identity is ResultAtom { Definition: MergeIdentity id } && c.Snapshot.Blocks.SelectMany(b => b.Merges)
                    .Single(m => m.Identity == id).Inputs.All(i => Check(i.Value));
            active.Remove(t); return result;
        }
        return Check(resolved.Value);
    }
}
