namespace Cpp2CS.Native;

public sealed record AsyncBodyNode(ulong Address, string Kind, string? Text, ulong[] Successors);
public sealed record AsyncBody(AsyncSource Source, AsyncBodyNode[] Nodes, string[] Proofs, string[] Problems, string? CSharp)
{
    [System.Text.Json.Serialization.JsonIgnore] public LiftResult? Projection { get; init; }
}

// 满足协议条件时收缩对应路径，保留协议外的调用、分支和异常。
public sealed class AsyncBodyRecovery(SsaSemantics semantics, NativeMethod method, ManagedNames managed,
    HeaderLayout layouts, Symbols symbols, Func<NativeMethod, SsaSemantics> lift)
{
    private readonly List<string> problems = [];
    private readonly List<string> proofs = [];
    private ManagedExpressionBuilder expressions = null!;
    private Dictionary<string, string> resultNames => expressions.Results;
    private HashSet<string> boolResults => expressions.BooleanResults;
    private readonly Dictionary<long, string> captures = [];
    private readonly Dictionary<string, AwaitSite> inlineResults = [];
    private readonly Dictionary<ulong, AsyncBodyNode> body = [];
    private readonly Dictionary<ulong, LiftedBlock> blocks = [];
    private LiftResult? projection;
    private readonly Dictionary<ulong, ulong> projected = [];
    private readonly HashSet<ulong> active = [];
    private readonly HashSet<SsaManagedStore> protocolStores = [];
    private readonly Dictionary<ulong, List<(SsaManagedStore Store, string Field, string Type)>> businessStores = [];
    private readonly Dictionary<int, ulong> restores = [];
    private SsaManagedCall[] calls = [];
    private SsaManagedStore[] stores = [];
    private AwaitSite[] sites = [];
    private Dictionary<ulong, NativeFlowNode> nodes = [];
    private SsaManagedCall? complete;
    private AsyncSource source = null!;
    private long stateOffset;
    private bool Need(bool ok, string why) { if (!ok) problems.Add(why); return ok; }
    private static T? Only<T>(IEnumerable<T> values) where T : class { var a = values.Take(2).ToArray(); return a.Length == 1 ? a[0] : null; }
    private static bool Same(SemanticTerm a, SemanticTerm b) => a.Key == b.Key;
    private static bool This(SemanticTerm v) => v is { Kind: "parameter", Name: "__this", Offset: 0 };
    private static IEnumerable<SemanticTerm> Terms(SemanticTerm v) => new[] { v }.Concat(v.Inputs.SelectMany(Terms));
    private static SemanticTerm[] Alternatives(SemanticTerm v) => v.Kind == "phi" ? v.Inputs.SelectMany(Alternatives).DistinctBy(x => x.Key).ToArray() : [v];
    private static bool Normal(NativeEdge e) => e.Kind is "next" or "branch" or "normal-return" or "taken" or "not-taken";
    private ulong[] Next(ulong pc) => nodes[pc].Edges.Where(Normal).Select(e => e.Target).OfType<ulong>().ToArray();
    private bool Reaches(ulong from, ulong to) => Walk([from], [to]).Contains(to);
    private bool BranchReaches(ulong pc, string edge, ulong target) => nodes[pc].Edges.Any(e => e.Kind == edge && e.Target is { } start && Reaches(start, target));
    private bool StateAddress(SemanticTerm value) => SsaSemantics.AddressParts(value) is var a && This(a.Root) && a.Offset == stateOffset;
    private HashSet<ulong> Frontier(IEnumerable<ulong> starts, HashSet<ulong> stops)
    {
        var region = Walk(starts, stops);
        return region.Where(pc => stops.Contains(pc) || nodes[pc].Instruction.Mnemonic == "ret").ToHashSet();
    }
    private HashSet<ulong> Walk(IEnumerable<ulong> starts, HashSet<ulong> stops)
    {
        var seen = new HashSet<ulong>(); var pending = new Stack<ulong>(starts);
        while (pending.TryPop(out var pc))
        {
            if (!seen.Add(pc) || stops.Contains(pc)) continue;
            foreach (var next in Next(pc)) pending.Push(next);
        }
        return seen;
    }
    public AsyncBody? Recover()
    {
        var owner = method.Name.Split("$$")[0];
        if (!managed.Implements(owner, "System.Runtime.CompilerServices.IAsyncStateMachine") || Only(managed.SourcesFor(owner)) is not { } original) return null;
        expressions = new(semantics, managed, layouts, symbols, problems.Add, proofs.Add) { Bind = BindExpression };
        source = original; calls = semantics.Calls(); stores = semantics.Stores();
        nodes = semantics.Program.Flow.Nodes.ToDictionary(n => n.Instruction.Address);
        var analysis = AwaitSites.Recover(semantics, symbols, layouts);
        sites = analysis.Sites;
        Need(semantics.Program.Problems.Length == 0 && semantics.Program.Flow.Problems.Length == 0, "SSA/控制流存在未支持操作");
        Need(calls.All(c => c.Kind != "indirect"), "存在未解析的间接调用");
        Need(sites.Length > 0 && sites.All(s => s.Problems.Length == 0 && s.Storage is not null && s.Producers.Length == 1 && s.StatusCandidates.Length == 1 && s.ResultCandidates.Length == 1), "await 数据流及消费调用未唯一确定");
        Need(analysis.Problems.Length == 0, "挂起状态冲突");
        var unsupportedRuntime = calls.Where(c => c.Kind == "runtime" && c.Name is not ("InitializeMetadata" or "ResolveMetadata" or "InitializeClass" or "EnsureClassMetadata" or
            "WriteBarrier" or "ResolveInterface" or "CxxBeginCatch" or "CxxEndCatch" or "IsAssignable" or "CxxAllocateException" or "CxxThrow" or
            "UnwindResume" or "CxxCatchTerminate" or "ThrowNullReference")).ToArray();
        foreach (var call in unsupportedRuntime) problems.Add($"0x{call.Address:x}: async 主体尚未归约运行时操作 {call.Name}");
        if (calls.Count(c => c.Name == "CxxBeginCatch") > 1)
            problems.Add("async 主体含业务或嵌套异常区域，不能按单一 builder 异常出口折叠；需保留捕获分支与各路径返回值");
        complete = Only(calls.Where(c => c.Kind == "interface" && c.Name.Contains("IStateMachineRunnerPromise") && c.Name.EndsWith(".SetResult")));
        var fail = Only(calls.Where(c => c.Kind == "interface" && c.Name.Contains("IStateMachineRunnerPromise") && c.Name.EndsWith(".SetException")));
        if (!Need(complete is not null && fail is not null, "builder 完成/异常出口不唯一") || problems.Count != 0) return Finish(null);
        var protocolCalls = sites.SelectMany(s => s.StatusCandidates.Concat(s.ResultCandidates)).Append(complete!.Address).Append(fail!.Address).ToHashSet();
        Need(calls.Where(c => c.Kind == "interface").All(c => protocolCalls.Contains(c.Address)), "存在协议之外的接口调用");
        stateOffset = sites[0].StateOffset!.Value;
        Need(sites.All(s => s.StateOffset == stateOffset), "挂起点未使用同一状态字段");
        BindCaptures();
        foreach (var site in sites) ProveAwait(site);
        ProveExceptionExit(fail!);
        ProveStateAndEffects(fail!);
        if (problems.Count != 0) return Finish(null);
        var entry = Project(semantics.Program.Flow.Entry);
        Need(calls.Where(c => c.Kind is "managed" or "virtual" && !AwaitSites.IsSchedule(c)).All(c => body.ContainsKey(c.Address)), "业务调用未被完整投影");
        Need(businessStores.Keys.All(body.ContainsKey), "业务字段写入未被完整投影");
        if (problems.Count != 0) return Finish(null);
        var declaration = $"public {(source.Static ? "static " : "")}async {source.ReturnType} {source.Name}({string.Join(", ", source.ParameterTypes.Zip(source.ParameterNames, (t, n) => t + " " + n))})";
        var sourceMethod = new NativeMethod(entry, source.Owner + "$$" + source.Name, source.ReturnType,
            source.ParameterTypes.Zip(source.ParameterNames, (type, name) => new NativeParameter(type, name)).ToArray(), declaration);
        var instructions = semantics.Program.Flow.Nodes.Select(n => n.Instruction).ToArray();
        var noReturn = semantics.Program.Flow.Nodes.Where(n => n.Instruction.Mnemonic == "bl" && n.Edges.All(e => e.Kind != "normal-return"))
            .Select(n => NativeGraph.Target(n.Instruction)).ToHashSet();
        projection = new(sourceMethod, instructions, blocks, [], [], new NativeGraph(instructions, noReturn.Contains))
        { SourceDeclaration = declaration, IsSourceProjection = true, RecoveryPath = "ssa-async" };
        SemanticValidation.Check(projection);
        problems.AddRange(projection.Problems);
        var text = problems.Count == 0 ? new SemanticWriter(symbols).Structured(projection) : null;
        proofs.Add("all projected business branches and calls retained; only verified await protocol paths contracted");
        return Finish(problems.Count == 0 ? text : null);
    }
    private AsyncBody Finish(string? text) => new(source, body.Values.OrderBy(n => n.Address).ToArray(), proofs.ToArray(), problems.Distinct().ToArray(), text)
    { Projection = text is null ? null : projection };
    private void BindCaptures()
    {
        var kickoff = Only(symbols.NamedMethods.GetValueOrDefault(source.Owner + "$$" + source.Name, []).Where(m =>
            m.Parameters.Where(p => p.Name is not ("__this" or "method")).Select(p => p.Name).SequenceEqual(source.ParameterNames)));
        if (!Need(kickoff is not null, "入口签名没有唯一匹配")) return;
        var entry = lift(kickoff!);
        var invocation = Only(entry.Calls().Where(c => c.Name == method.Name));
        if (!Need(invocation is not null, "入口未直接调用已确认的状态机")) return;
        var (frame, origin) = SsaSemantics.AddressParts(invocation!.Arguments[0]);
        if (!Need(frame.Kind == "stack", "入口状态机存储未定位")) return;
        foreach (var store in entry.Stores().Where(s => s.Address < invocation.Address))
        {
            var (root, offset) = SsaSemantics.AddressParts(store.AddressValue);
            if (!Same(root, frame)) continue;
            var value = store.Value;
            while (value.Kind is "slice" or "zero-extend" or "sign-extend" or "abi-extend" && value.Offset == 0) value = value.Inputs[0];
            if (value is { Kind: "and", Inputs: [var bits, { Kind: "constant", Offset: 1 }] })
            {
                while (bits.Kind is "slice" or "zero-extend" or "abi-extend" && bits.Offset == 0) bits = bits.Inputs[0];
                if (bits is { Kind: "parameter", Type: "bool" }) value = bits;
            }
            if (value.Kind == "parameter") captures[offset - origin] = value.Name == "__this" ? "this" : value.Name;
        }
        Need(entry.Stores().Any(s => s.Address < invocation.Address && SsaSemantics.AddressParts(s.AddressValue) is var a && Same(a.Root, frame) && a.Offset == origin + stateOffset &&
            s.Value is { Kind: "constant", Width: 32, Offset: 4294967295 }), "入口没有初始化 -1 运行状态");
    }
    private bool Restored(SemanticTerm value, AwaitSite site) => value.Width == site.AwaiterBytes * 8 &&
        (value is { Kind: "field", Inputs: [var root] } && This(root) && value.Offset == site.AwaiterOffset ||
         value is { Kind: "load", Inputs: [var address] } && SsaSemantics.AddressParts(address) is var a && This(a.Root) && a.Offset == site.AwaiterOffset);
    private void ProveAwait(AwaitSite site)
    {
        var status = calls.Single(c => c.Address == site.StatusCandidates[0]);
        var consume = calls.Single(c => c.Address == site.ResultCandidates[0]);
        var produced = site.Awaiter!; var storage = site.Storage!;
        Need(Same(status.Arguments[0], storage.ReadSource(produced)) && Same(SsaSemantics.Slice(status.Arguments[1], 0, 16), storage.ReadToken(produced)), $"0x{status.Address:x}: source/token 没有来自同一任务");
        var restored = Only(consume.Arguments.SelectMany(Terms).Where(t => Restored(t, site)).DistinctBy(t => t.Key));
        if (!Need(restored is not null, $"状态 {site.State}: 恢复值未绑定保存字段")) return;
        var sources = Alternatives(consume.Arguments[0]);
        var tokens = Alternatives(SsaSemantics.Slice(consume.Arguments[1], 0, 16));
        Need(sources.Length == 2 && sources.Any(t => Same(t, storage.ReadSource(produced))) && sources.Any(t => Same(t, storage.ReadSource(restored!))) &&
            tokens.Length == 2 && tokens.Any(t => Same(t, storage.ReadToken(produced))) && tokens.Any(t => Same(t, storage.ReadToken(restored!))) &&
            sources.Zip(tokens).All(p => p.First.Kind == "slice" && p.Second.Kind == "slice" && Same(p.First.Inputs[0], p.Second.Inputs[0])), $"状态 {site.State}: 恢复 source/token 的前驱配对失败");
        var restore = Only(semantics.Program.Values.Where(v => v.Operation == "load" && Same(semantics.Resolve(v.Id), restored!)));
        if (!Need(restore is not null, "恢复读取身份不唯一")) return;
        restores[site.State!.Value] = restore!.Address;
        var region = Walk([restore!.Address], [consume.Address]);
        var clears = stores.Where(s => region.Contains(s.Address) && s.Value is { Kind: "constant", Offset: 0 } && SsaSemantics.AddressParts(s.AddressValue) is var a && This(a.Root) &&
            a.Offset >= site.AwaiterOffset && a.Offset < site.AwaiterOffset + site.AwaiterBytes).OrderBy(s => SsaSemantics.AddressParts(s.AddressValue).Offset).ToArray();
        Need(clears.Sum(s => s.Value.Width) == site.AwaiterBytes * 8 && clears.Select((s, i) => SsaSemantics.AddressParts(s.AddressValue).Offset == site.AwaiterOffset + clears.Take(i).Sum(p => p.Value.Width / 8)).All(x => x), "awaiter 恢复后未完整清空");
        protocolStores.UnionWith(clears);
        protocolStores.UnionWith(stores.Where(s => SsaSemantics.AddressParts(s.AddressValue) is var a && This(a.Root) && a.Offset == site.AwaiterOffset && Same(s.Value, produced)));
        Need(stores.Any(s => region.Contains(s.Address) && StateAddress(s.AddressValue) && s.Value is { Kind: "constant", Width: 32, Offset: 4294967295 }), "恢复后没有运行状态 -1");
        var condition = Only(semantics.Program.Instructions.Where(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero" or "nonzero", Inputs: [var value] } &&
            Same(value, SsaSemantics.Slice(semantics.Resolve(status.Value), 0, 32))));
        var pendingEdge = condition is not null && semantics.Resolve(condition.Condition!).Kind == "zero" ? "taken" : "not-taken";
        Need(condition is not null && nodes[condition.Address].Edges.Any(e => e.Kind == pendingEdge && e.Target is { } t && Reaches(t, site.Schedule)) &&
            !nodes[condition!.Address].Edges.Any(e => Normal(e) && e.Kind != pendingEdge && e.Target is { } t && Reaches(t, site.Schedule)), "Pending 分支没有正确进入调度");
        var producer = calls.Single(c => c.Address == site.Producers[0]);
        var allowed = new HashSet<ulong> { status.Address, consume.Address, site.Schedule };
        var stops = calls.Where(c => c.Address != producer.Address && c.Kind is "managed" or "virtual" && !AwaitSites.IsSchedule(c)).Select(c => c.Address)
            .Concat(stores.Where(s => This(s.AddressValue) && s.Value is { Kind: "constant", Width: 32, Offset: 4294967294 }).Select(s => s.Address))
            .Concat(calls.Where(c => c.Name == "ThrowNullReference").Select(c => c.Address)).Append(consume.Address).ToHashSet();
        var protocol = Walk(Next(producer.Address), stops);
        var extra = calls.Where(c => protocol.Contains(c.Address) && !stops.Contains(c.Address) && !allowed.Contains(c.Address) && !(c.Kind == "runtime" && c.Name is "InitializeMetadata" or "InitializeClass" or "EnsureClassMetadata" or "WriteBarrier" or "ResolveInterface")).ToArray();
        Need(extra.Length == 0, "await 协议区包含未归约调用：" + string.Join(',', extra.Select(c => $"0x{c.Address:x}:{c.Name}")));
        var guards = new Dictionary<ulong, ulong>();
        foreach (var operation in new[] { consume, status })
            Need(semantics.Program.Instructions.Any(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero", Inputs: [var receiver] } && Same(receiver, operation.Arguments[0]) &&
                nodes[i.Address].Edges.Any(e => e.Kind == "not-taken" && e.Target is { } t && Reaches(t, operation.Address)) &&
                !nodes[i.Address].Edges.Any(e => e.Kind == "taken" && e.Target is { } t && Reaches(t, operation.Address))), "await source 的空路径未证明");
        var boundaries = calls.Where(c => c.Kind is "managed" or "virtual" or "interface" || c.Name == "ThrowNullReference").Select(c => c.Address)
            .Concat(stores.Where(s => StateAddress(s.AddressValue) && s.Value is { Kind: "constant", Offset: 4294967294 }).Select(s => s.Address)).ToHashSet();
        var continuation = Frontier(Next(consume.Address), boundaries);
        foreach (var operation in new[] { consume, status })
        {
            var guard = Only(semantics.Program.Instructions.Where(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero", Inputs: [var receiver] } &&
                Same(receiver, operation.Arguments[0]) && BranchReaches(i.Address, "not-taken", operation.Address) && !BranchReaches(i.Address, "taken", operation.Address)));
            if (guard is not null)
            {
                guards[operation.Address] = guard.Address;
                var bypass = Frontier(nodes[guard.Address].Edges.Where(e => e.Kind == "taken").Select(e => e.Target!.Value), boundaries);
                var throughConsumeGuard = operation == status && guards.TryGetValue(consume.Address, out var consumeGuard) &&
                    Frontier(nodes[guard.Address].Edges.Where(e => e.Kind == "taken").Select(e => e.Target!.Value), boundaries.Append(consumeGuard).ToHashSet()).SetEquals([consumeGuard]);
                Need(bypass.SetEquals(continuation) || throughConsumeGuard, $"0x{operation.Address:x}: source 空路径与 GetResult 后继不一致");
            }
        }
        var scheduled = Frontier(Next(site.Schedule), boundaries);
        Need(scheduled.Count > 0 && scheduled.All(pc => nodes[pc].Instruction.Mnemonic == "ret"), "调度后仍有业务执行或其他协议调用");
        if (storage.Result is not null)
        {
            var name = "awaited" + Array.IndexOf(sites, site);
            resultNames[consume.Value] = name;
            if (storage.Result.Type == "bool") boolResults.Add(name);
            inlineResults[produced.Key] = site;
            inlineResults[restored!.Key] = site;
        }
        proofs.Add($"state {site.State}: paired source/token, full spill/reload/clear, Pending schedule and isolated protocol region");
    }
    private void ProveStateAndEffects(SsaManagedCall fail)
    {
        var stateStores = stores.Where(s => SsaSemantics.AddressParts(s.AddressValue) is var a && This(a.Root) && a.Offset == stateOffset && s.Value.Width == 32).ToArray();
        var expected = sites.Select(s => (long)s.State!.Value).Concat(Enumerable.Repeat((long)uint.MaxValue, sites.Length)).Concat([4294967294L, 4294967294L]).Order().ToArray();
        Need(stateStores.All(s => s.Value.Kind == "constant") && stateStores.Select(s => s.Value.Offset).Order().SequenceEqual(expected), "状态写入集合与挂起/恢复/两个完成出口不匹配");
        protocolStores.UnionWith(stateStores);
        var exitEvents = calls.Where(c => c.Kind is "managed" or "virtual" or "interface").Select(c => c.Address).ToHashSet();
        foreach (var terminal in stateStores.Where(s => s.Value.Offset == 4294967294))
        {
            var successors = Frontier(Next(terminal.Address), exitEvents);
            var exit = Reaches(terminal.Address, complete!.Address) ? complete : fail;
            Need(successors.Contains(exit.Address) && successors.All(pc => pc == exit.Address || nodes[pc].Instruction.Mnemonic == "ret"), "完成状态写入后仍有未归约业务");
        }
        var events = calls.Where(c => c.Kind is "managed" or "virtual").Select(c => c.Address).Concat(restores.Values).ToHashSet();
        foreach (var (state, restore) in restores)
        {
            var found = new HashSet<ulong>(); var seen = new HashSet<ulong>(); var pending = new Stack<ulong>(); pending.Push(semantics.Program.Flow.Entry);
            while (pending.TryPop(out var pc))
            {
                if (!seen.Add(pc)) continue;
                if (events.Contains(pc)) { found.Add(pc); continue; }
                var instruction = semantics.Program.Instructions.Single(i => i.Address == pc);
                if (instruction.Condition is { } condition && EvaluateState(semantics.Resolve(condition), state) is { } known)
                    pending.Push(nodes[pc].Edges.Single(e => e.Kind == (known ? "taken" : "not-taken")).Target!.Value);
                else foreach (var next in Next(pc)) pending.Push(next);
            }
            Need(found.SetEquals([restore]), $"状态 {state}: 恢复入口可能误入其他 await 或业务调用");
        }
        var schedule = calls.Single(c => c.Address == sites[0].Schedule);
        var builderType = semantics.TargetMethod(schedule.Value)!.Parameters[0].Type.TrimEnd('*');
        var builderOffset = SsaSemantics.AddressParts(schedule.Arguments[0]).Offset;
        var builderFields = layouts.Flatten(builderType, 0).ToArray();
        foreach (var store in stores.Where(s => !protocolStores.Contains(s)))
        {
            var (root, offset) = SsaSemantics.AddressParts(store.AddressValue);
            if (root.Kind == "stack") continue;
            if (This(root))
            {
                var field = builderFields.SingleOrDefault(f => f.Offset + builderOffset == offset && f.Size * 8 == store.Value.Width);
                if (field is not null && symbols.Display(field.Type) == "System.Exception" && Same(store.Value, fail.Arguments[1])) continue;
                if (field?.Name == "result" && complete!.Arguments.Length == 2 && Expression(store.Value) == Expression(complete.Arguments[1])) continue;
                problems.Add($"0x{store.Address:x}: 状态机有额外写入"); continue;
            }
            var metadataFlag = root.Kind == "constant" && store.Value is { Kind: "constant", Width: 8, Offset: 1 } && semantics.Program.Instructions.Any(i => i.Condition is { } c &&
                Terms(semantics.Resolve(c)).Any(t => t is { Kind: "load", Width: 8, Inputs: [var a] } && Same(a, store.AddressValue)));
            var wrapper = root.Kind == "call-result" && calls.Any(c => c.Value == root.Name && c.Name == "CxxAllocateException") &&
                store.Value is { Kind: "load", Inputs: [{ Kind: "call-result" } caught] } && calls.Any(c => c.Value == caught.Name && c.Name == "CxxBeginCatch");
            if (metadataFlag || wrapper) continue;
            var member = root.Type is { } native && native.EndsWith('*') ? layouts.ContainingField(native, checked((int)offset), store.Value.Width / 8) : null;
            var owner = root.Type is null ? "" : symbols.Display(root.Type);
            if (member is not null && member.Type is "bool" or "int32_t" or "int64_t" &&
                (member.Type != "bool" || store.Value is { Kind: "constant", Offset: 0 or 1 }) &&
                managed.MutableField(owner, member.Name) is { } fieldName && member.Path.Where(p => p != "fields").SequenceEqual([member.Name]))
            {
                if (!businessStores.TryGetValue(store.Address, out var writes)) businessStores[store.Address] = writes = [];
                writes.Add((store, fieldName, member.Type));
                continue;
            }
            Need(false, $"0x{store.Address:x}: 协议之外有内存写入");
        }
    }
    private void ProveExceptionExit(SsaManagedCall fail)
    {
        var begin = Only(calls.Where(c => c.Name == "CxxBeginCatch"));
        var assignable = Only(calls.Where(c => c.Name == "IsAssignable"));
        if (!Need(begin is not null && assignable is not null && assignable.Arguments[0] is { Kind: "metadata", Name: "System.Exception_TypeInfo" }, "异常类型捕获未证明")) return;
        Need(fail.Arguments[1] is { Kind: "load", Inputs: [var wrapper] } && wrapper.Kind == "call-result" && wrapper.Name == begin!.Value, "SetException 值不是捕获的托管异常");
        var protectedCalls = calls.Where(c => c.Kind is "managed" or "virtual" || sites.Any(s => s.StatusCandidates.Contains(c.Address) || s.ResultCandidates.Contains(c.Address)));
        foreach (var call in protectedCalls)
            Need(nodes[call.Address].Edges.Any(e => e.Kind == "exception-dispatch" && e.Target is { } pad && Reaches(pad, begin!.Address)), $"0x{call.Address:x}: 调用不在共同异常捕获区");
        Need(new[] { complete!, fail }.All(c => !nodes[c.Address].Edges.Any(e => e.Kind == "exception-dispatch")), "builder 出口不能放回主体捕获区");
        Need(complete!.Arguments[0] is { Kind: "field" } done && fail.Arguments[0] is { Kind: "field" } failed && done.Offset == failed.Offset && Same(done.Inputs[0], failed.Inputs[0]), "完成和异常出口没有共同 builder");
        Need(calls.Any(c => c.Name == "UnwindResume") && calls.Any(c => c.Name == "CxxThrow"), "缺少原生异常展开出口");
        Need(assignable!.Arguments[1] is { Kind: "load", Inputs: [{ Kind: "load", Inputs: [var typedWrapper] }] } &&
            typedWrapper.Kind == "call-result" && typedWrapper.Name == begin!.Value, "异常类型检查没有使用同一对象");
        var rethrow = Only(calls.Where(c => c.Name == "CxxThrow"));
        if (rethrow is null) return;
        var filters = nodes.Values.SelectMany(n => n.Edges).Where(e => e.Kind == "exception-dispatch" && e.Region is not null)
            .SelectMany(e => e.Region!.Actions).Where(a => a.Kind == "typed-catch").Select(a => a.TypeInfo).Distinct().ToArray();
        Need(filters.Length == 1 && rethrow.Arguments[1] is { Kind: "constant" } rtti && (ulong)rtti.Offset == filters[0], "原生重抛类型与 LSDA 不匹配");
        Need(semantics.Program.Instructions.Any(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero" } zero &&
            Terms(zero).Any(t => t.Kind == "call-result" && t.Name == assignable.Value) && BranchReaches(i.Address, "taken", rethrow.Address) &&
            !BranchReaches(i.Address, "taken", fail.Address) && BranchReaches(i.Address, "not-taken", fail.Address)), "类型不匹配路径没有重抛");
        foreach (var exit in new[] { complete!, fail })
            Need(semantics.Program.Instructions.Any(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero", Inputs: [var receiver] } &&
                Same(receiver, exit.Arguments[0]) && BranchReaches(i.Address, "not-taken", exit.Address) && !BranchReaches(i.Address, "taken", exit.Address)), "builder 出口缺少空 runner 路径");
    }
    private ulong Project(ulong pc)
    {
        if (projected.TryGetValue(pc, out var cached)) return cached;
        if (!active.Add(pc)) { problems.Add($"0x{pc:x}: 业务循环尚未结构化"); return 0; }
        ulong result;
        var call = calls.SingleOrDefault(c => c.Address == pc);
        var site = sites.SingleOrDefault(s => s.Producers.Contains(pc));
        if (stores.Any(s => s.Address == pc && StateAddress(s.AddressValue) && s.Value is { Kind: "constant", Width: 32, Offset: 4294967294 }))
        {
            result = pc;
            var expression = complete!.Arguments.Length > 1 ? expressions.Value(complete.Arguments[1]) : null;
            AddBlock(pc, "return", [new ReturnStatement(pc, expression)], null, []);
        }
        else if (call?.Name == "ThrowNullReference") { result = pc; AddBlock(pc, "throw", [new ThrowStatement(pc, "System.NullReferenceException")], null, []); }
        else if (businessStores.TryGetValue(pc, out var writes))
        {
            result = pc;
            var assignments = writes.Select(w =>
            {
                var target = new SourceMemberExpression(expressions.Value(SsaSemantics.AddressParts(w.Store.AddressValue).Root), w.Field, w.Type);
                return (Statement)new StoreStatement(pc, target, expressions.TypedValue(w.Store.Value, w.Type));
            }).ToList();
            AddBlock(pc, "store", assignments, null, [Project(Next(pc).Single())]);
        }
        else if (call is { Kind: "managed" or "virtual" })
        {
            result = pc;
            var statements = new List<Statement>();
            var expression = expressions.Call(call, statements);
            var next = site is null ? Next(pc).Single() : Next(site.ResultCandidates.Single()).Single();
            if (site is not null)
            {
                expression = new AwaitExpression(expression);
                statements.Add(site.Storage!.Result is null ? new EvaluateStatement(pc, expression) :
                    new AssignStatement(pc, resultNames[calls.Single(c => c.Address == site.ResultCandidates[0]).Value], expression, site.Storage.Result.Type));
            }
            else if (call.ReturnType == "void") statements.Add(new EvaluateStatement(pc, expression));
            else
            {
                var name = "value" + calls.Where(c => c.Kind is "managed" or "virtual").TakeWhile(c => c.Address != pc).Count();
                resultNames[call.Value] = name;
                statements.Add(new AssignStatement(pc, name, expression, call.ReturnType!));
            }
            AddBlock(pc, site is null ? "call" : "await", statements, null, [Project(next)]);
        }
        else
        {
            var next = Next(pc);
            var condition = semantics.Program.Instructions.Single(i => i.Address == pc).Condition;
            if (condition is not null && EvaluateState(semantics.Resolve(condition)) is { } known)
                result = Project(nodes[pc].Edges.Single(e => e.Kind == (known ? "taken" : "not-taken")).Target!.Value);
            else if (next.Length == 1) result = Project(next[0]);
            else if (next.Length == 2 && condition is not null)
            {
                var yes = Project(nodes[pc].Edges.Single(e => e.Kind == "taken").Target!.Value);
                var no = Project(nodes[pc].Edges.Single(e => e.Kind == "not-taken").Target!.Value);
                if (yes == no) result = yes;
                else { result = pc; AddBlock(pc, "branch", [], expressions.Value(semantics.Resolve(condition)), [yes, no]); }
            }
            else { problems.Add($"0x{pc:x}: 未覆盖的控制流出口"); result = 0; }
        }
        active.Remove(pc); projected[pc] = result; return result;
    }
    private void AddBlock(ulong address, string kind, List<Statement> statements, Expression? condition, ulong[] successors)
    {
        blocks[address] = new(address, statements, condition, successors);
        body[address] = new(address, kind, condition is null ? string.Join("\n", statements.Select(SemanticWriter.Statement)) : SemanticWriter.Expression(condition), successors);
    }
    private Expression? BindExpression(SemanticTerm value)
    {
        if (value is { Kind: "field", Inputs: [var root] } && This(root) && captures.TryGetValue(value.Offset, out var capture))
            return new NameExpression(capture);
        if (value is { Kind: "slice", Inputs: [var task] } && inlineResults.TryGetValue(task.Key, out var site) &&
            site.Storage!.Result is { } field && value.Offset == field.Offset * 8 && value.Width == field.Size * 8)
            return new NameExpression(resultNames[calls.Single(c => c.Address == site.ResultCandidates[0]).Value]);
        return null;
    }
    private bool? EvaluateState(SemanticTerm term, int state = -1)
    {
        long? Value(SemanticTerm v) => v.Kind == "constant" ? v.Offset : v is { Kind: "field", Width: 32, Inputs: [var root] } && This(root) && v.Offset == stateOffset ? unchecked((uint)state) :
            v.Kind is "slice" or "zero-extend" && v.Offset == 0 ? Value(v.Inputs[0]) : null;
        if (term.Kind is "zero" or "nonzero" && Value(term.Inputs[0]) is { } number) return (number == 0) == (term.Kind == "zero");
        if (term.Kind is "b.eq" or "b.ne" && term.Inputs[0] is { Kind: "compare", Inputs: [var left, var right] } && Value(left) is { } a && Value(right) is { } b)
            return (a == b) == (term.Kind == "b.eq");
        return null;
    }
    private string Expression(SemanticTerm value) => SemanticWriter.Expression(expressions.Value(value));
}
