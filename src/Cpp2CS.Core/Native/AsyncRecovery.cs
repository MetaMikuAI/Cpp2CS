namespace Cpp2CS.Native;

public sealed record AsyncProtocol(AsyncSource Source, string AwaitedCall, string Constructor, string[] Arguments,
    long StateOffset, long AwaiterOffset, int AwaiterBytes, ulong Schedule, ulong Complete, ulong Fail,
    string[] Proofs, string[] Problems, string? CSharp)
{
    [System.Text.Json.Serialization.JsonIgnore] public LiftResult? Projection { get; init; }
}

// 单个 await 的协议归约。所有数据都来自 SSA，识别范围由协议决定，不由业务方法决定。
public sealed class AsyncRecovery(SsaSemantics semantics, NativeMethod method, ManagedNames managed, HeaderLayout layouts,
    Symbols symbols, Func<NativeMethod, SsaSemantics> lift)
{
    private readonly List<string> problems = [];
    private readonly List<string> proofs = [];
    private NativeControlFlow Flow => semantics.Program.Flow;
    private bool Require(bool condition, string message) { if (!condition) problems.Add(message); return condition; }
    private static T? Only<T>(IEnumerable<T> values) where T : class { var items = values.Take(2).ToArray(); return items.Length == 1 ? items[0] : null; }
    private static bool IsThis(SemanticTerm value) => value is { Kind: "parameter", Name: "__this", Offset: 0 };
    private static bool AtThis(SemanticTerm value, long offset) => SsaSemantics.AddressParts(value) is var a && IsThis(a.Root) && a.Offset == offset;
    private static SemanticTerm Low(SemanticTerm value, int width) => SsaSemantics.Slice(value, 0, width);
    private static bool Equal(SemanticTerm left, SemanticTerm right) => left.Key == right.Key;
    private static bool SameField(SemanticTerm left, SemanticTerm right) => left.Kind == "field" && right.Kind == "field" &&
        left.Offset == right.Offset && left.Width == right.Width && left.Type == right.Type && Equal(left.Inputs[0], right.Inputs[0]);
    private static SemanticTerm[] Alternatives(SemanticTerm value) => value.Kind == "phi" ? value.Inputs.SelectMany(Alternatives).DistinctBy(v => v.Key).ToArray() : [value];
    private static IEnumerable<SemanticTerm> Descendants(SemanticTerm value) => new[] { value }.Concat(value.Inputs.SelectMany(Descendants));
    public AsyncProtocol? Recover()
    {
        var owner = method.Name.Split("$$")[0];
        if (!managed.Implements(owner, "System.Runtime.CompilerServices.IAsyncStateMachine")) return null;
        var source = Only(managed.SourcesFor(owner));
        if (source is null) return null;
        var calls = semantics.Calls(); var stores = semantics.Stores();
        var schedule = Only(calls.Where(c => c.Kind == "managed" && c.Name.StartsWith("Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder$$AwaitUnsafeOnCompleted<")));
        var status = Only(calls.Where(c => c.Kind == "interface" && c.Name == "Cysharp.Threading.Tasks.IUniTaskSource.GetStatus"));
        var consume = Only(calls.Where(c => c.Kind == "interface" && c.Name == "Cysharp.Threading.Tasks.IUniTaskSource.GetResult"));
        var complete = Only(calls.Where(c => c.Kind == "interface" && c.Name == "Cysharp.Threading.Tasks.CompilerServices.IStateMachineRunnerPromise.SetResult"));
        var fail = Only(calls.Where(c => c.Kind == "interface" && c.Name == "Cysharp.Threading.Tasks.CompilerServices.IStateMachineRunnerPromise.SetException"));
        if (!Require(schedule is not null && status is not null && consume is not null && complete is not null && fail is not null,
            "尚未证明完整的单 await UniTask 协议调用")) return Result(source);
        var work = Only(calls.Where(c => c.Kind == "managed" && c != schedule && c.ReturnType is { } t && symbols.Display(t) == source.ReturnType));
        var constructor = Only(calls.Where(c => c.Kind == "managed" && c.Name.EndsWith("$$.ctor")));
        if (!Require(work is not null && constructor is not null, "业务值的生产者或构造调用不唯一")) return Result(source);
        if (!Require(source.ReturnType == "Cysharp.Threading.Tasks.UniTask" && work!.Arguments.Length >= 2 &&
            work.Arguments[0].Kind == "new-object" && Equal(work.Arguments[0], constructor!.Arguments[0]) && constructor.Arguments.Length == 2 &&
            constructor.Arguments[1] is { Kind: "constant", Offset: 0 }, "尚未支持该 await 生产者的构造形式")) return Result(source);
        Require(calls.Where(c => c.Kind == "managed").All(c => c == work || c == constructor || c == schedule), "存在协议之外的托管调用");
        Require(calls.All(c => c.Kind != "indirect"), "仍有未解析调用");
        Require(semantics.Program.Problems.Length == 0 && Flow.Problems.Length == 0, "机器 IR 存在未支持操作");
        var signature = semantics.TargetMethod(work!.Value)!;
        Require(work.Arguments.Skip(1).SkipLast(1).Select((a, i) => a.Type == signature.Parameters[i + 1].Type).All(x => x), "await 参数类型与被调用者签名不一致");
        var produced = SsaSemantics.Term("call-result", layouts.Size(work!.ReturnType!) * 8, work.Value, type: work.ReturnType);
        var storage = UniTaskStorage.Read(work.ReturnType!, symbols, layouts);
        if (!Require(storage is not null, "UniTask 的 source/token/result 布局未确认")) return Result(source);
        var sourceField = storage!.Source;
        var tokenField = storage.Token;
        var producedSource = SsaSemantics.Slice(produced, sourceField!.Offset * 8, sourceField.Size * 8);
        var producedToken = SsaSemantics.Slice(produced, tokenField!.Offset * 8, tokenField.Size * 8);
        Require(Equal(status!.Arguments[0], producedSource) && Equal(Low(status.Arguments[1], 16), producedToken), "GetStatus 参数并非来自同一个返回聚合值");
        var save = Only(stores.Where(s => Equal(s.Value, produced) && IsThis(SsaSemantics.AddressParts(s.AddressValue).Root)));
        if (!Require(save is not null, "未找到完整 awaiter 保存")) return Result(source);
        var awaiterOffset = SsaSemantics.AddressParts(save!.AddressValue).Offset;
        var restored = Only(consume!.Arguments.SelectMany(Descendants).Where(v => v.Kind == "field" && v.Offset == awaiterOffset && v.Width == produced.Width).DistinctBy(v => v.Key));
        if (!Require(restored is not null, "未找到与保存字段匹配的 awaiter 恢复")) return Result(source);
        var consumedSources = Alternatives(consume.Arguments[0]);
        var restoredSource = SsaSemantics.Slice(restored!, sourceField.Offset * 8, sourceField.Size * 8);
        Require(consumedSources.Length == 2 && consumedSources.Any(v => Equal(v, producedSource)) && consumedSources.Any(v => Equal(v, restoredSource)), "GetResult 的 source 合流不完整");
        var tokens = Alternatives(Low(consume.Arguments[1], 16));
        Require(tokens.Length == 2 && tokens.Any(v => Equal(v, producedToken)) && tokens.Any(v => Equal(v, SsaSemantics.Slice(restored!, tokenField.Offset * 8, tokenField.Size * 8))), "GetResult 的 token 合流不完整");
        Require(consumedSources.Length == tokens.Length && consumedSources.Zip(tokens).All(pair => pair.First.Kind == "slice" && pair.Second.Kind == "slice" && Equal(pair.First.Inputs[0], pair.Second.Inputs[0])), "source/token 的前驱配对不一致");
        var stateStores = stores.Where(s => s.Value.Width == 32 && s.Value.Kind == "constant" && IsThis(SsaSemantics.AddressParts(s.AddressValue).Root)).ToArray();
        var stateOffsets = stateStores.Select(s => SsaSemantics.AddressParts(s.AddressValue).Offset).Distinct().ToArray();
        if (!Require(stateOffsets.Length == 1, "状态字段不唯一")) return Result(source);
        var stateOffset = stateOffsets[0];
        Require(stateStores.Select(s => unchecked((int)s.Value.Offset)).Order().SequenceEqual(new[] { -2, -2, -1, 0 }), "状态写入不符合单 await 协议");
        var clears = stores.Where(s => s.Value is { Kind: "constant", Offset: 0 } && SsaSemantics.AddressParts(s.AddressValue) is var a && IsThis(a.Root) && a.Offset >= awaiterOffset && a.Offset < awaiterOffset + produced.Width / 8).OrderBy(s => SsaSemantics.AddressParts(s.AddressValue).Offset).ToArray();
        Require(clears.Sum(s => s.Value.Width) == produced.Width && clears.Select((s, index) => SsaSemantics.AddressParts(s.AddressValue).Offset == awaiterOffset + clears.Take(index).Sum(p => p.Value.Width / 8)).All(x => x), "恢复后 awaiter 未完整清零");
        Require(schedule!.Arguments.Length == 4 && IsThis(schedule.Arguments[2]) && SsaSemantics.AddressParts(schedule.Arguments[1]).Root.Kind == "stack", "调度调用的 ref awaiter/ref stateMachine 参数不一致");
        Require(Equal(semantics.LoadAtCall(schedule.Value, schedule.Arguments[1], produced.Width / 8), produced), "调度调用没有传入完整的本地 awaiter");
        Require(AtThis(schedule.Arguments[0], complete!.Arguments[0].Offset) && SameField(complete.Arguments[0], fail!.Arguments[0]), "完成和异常出口没有使用同一个 builder");
        var condition = Only(semantics.Program.Instructions.Where(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero", Inputs: [var input] } &&
            input.Width == 32 && Equal(input, Low(semantics.Resolve(status.Value), 32))));
        Require(condition is not null && BranchReaches(condition.Address, "taken", schedule.Address) && !BranchReaches(condition.Address, "not-taken", schedule.Address), "Pending 分支没有唯一进入挂起路径");
        var stateCondition = Only(semantics.Program.Instructions.Where(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero", Inputs: [var field] } && field.Kind == "field" && field.Offset == stateOffset && field.Width == 32 && IsThis(field.Inputs[0])));
        Require(stateCondition is not null && clears.Length > 0 && BranchReaches(stateCondition.Address, "taken", clears[0].Address) &&
            !BranchReaches(stateCondition.Address, "taken", work.Address) && BranchReaches(stateCondition.Address, "not-taken", work.Address), "入口状态分支不能证明首次执行与恢复执行");
        Require(NullGuard(status.Arguments[0], status.Address) && NullGuard(consume.Arguments[0], consume.Address), "source == null 的完成路径不符合 awaiter 协议");
        Require(NullGuard(complete.Arguments[0], complete.Address) && NullGuard(fail!.Arguments[0], fail.Address), "builder runner 的空引用分支不符合协议");
        ValidateExceptions(calls, work, constructor!, schedule, status, consume, complete, fail!);
        ValidateFlow(calls, stores, stateStores, clears, restored!, save, work, constructor!, status, consume, schedule, complete, fail!);
        var captured = BindSource(source, owner, work, stateOffset);
        if (captured is null) return Result(source);
        var objectType = constructor!.Name.Split("$$")[0];
        var methodName = work.Name.Split("$$")[1];
        var expression = new InvocationExpression(methodName, new InvocationExpression("new " + objectType, null, [], false),
            captured.Select(name => (Expression)new NameExpression(name)).ToArray(), false);
        var declaration = $"public {(source.Static ? "static " : "")}async {source.ReturnType} {source.Name}({string.Join(", ", source.ParameterTypes.Zip(source.ParameterNames, (type, name) => type + " " + name))})";
        proofs.Add("SSA source/token slices retain the same aggregate producer across spill, interface calls and state-machine field copies");
        proofs.Add("AsyncStateMachineAttribute source identity and kickoff stores map captured fields to original parameters");
        proofs.Add("state 0 resumes saved awaiter; -1 restores running state; -2 completes; Pending branch schedules once");
        proofs.Add("SetResult/SetException stay outside the protected body; generated method uses the original UniTask builder contract");
        if (problems.Count != 0) proofs.Clear();
        LiftResult? projection = null;
        string? text = null;
        if (problems.Count == 0)
        {
            var sourceMethod = new NativeMethod(method.Address, source.Owner + "$$" + source.Name, source.ReturnType,
                source.ParameterTypes.Zip(source.ParameterNames, (type, name) => new NativeParameter(type, name)).ToArray(), declaration);
            var instructions = Flow.Nodes.Select(n => n.Instruction).ToArray();
            projection = new(sourceMethod, instructions,
                new() { [method.Address] = new(method.Address, [new EvaluateStatement(work.Address, new AwaitExpression(expression))], null, []) },
                [], [], new NativeGraph(instructions, _ => false))
            { SourceDeclaration = declaration, IsSourceProjection = true, RecoveryPath = "ssa-async-single" };
            SemanticValidation.Check(projection);
            problems.AddRange(projection.Problems);
            if (problems.Count == 0) text = new SemanticWriter(symbols).Structured(projection);
        }
        return new(source, work.Name, constructor.Name, captured, stateOffset, awaiterOffset, produced.Width / 8,
            schedule.Address, complete.Address, fail!.Address, proofs.ToArray(), problems.ToArray(), text)
        { Projection = text is null ? null : projection };
    }
    private AsyncProtocol Result(AsyncSource source) => new(source, "", "", [], 0, 0, 0, 0, 0, 0, proofs.ToArray(), problems.ToArray(), null);
    private void ValidateFlow(SsaManagedCall[] calls, SsaManagedStore[] stores, SsaManagedStore[] stateStores,
        SsaManagedStore[] clears, SemanticTerm restored, SsaManagedStore save, SsaManagedCall work, SsaManagedCall constructor,
        SsaManagedCall status, SsaManagedCall consume, SsaManagedCall schedule, SsaManagedCall complete, SsaManagedCall fail)
    {
        var events = new Dictionary<ulong, string>();
        var allocation = Only(calls.Where(c => c.Value == work.Arguments[0].Name));
        var restore = Only(semantics.Program.Values.Where(v => v.Operation == "load" && Equal(semantics.Resolve(v.Id), restored)));
        if (!Require(allocation is not null && restore is not null, "构造或恢复事件身份不唯一")) return;
        events[allocation!.Address] = "allocate"; events[constructor.Address] = "construct"; events[work.Address] = "produce";
        events[status.Address] = "status"; events[consume.Address] = "consume"; events[schedule.Address] = "schedule";
        events[complete.Address] = "complete"; events[fail.Address] = "fail"; events[restore!.Address] = "restore";
        events[save.Address] = "save";
        foreach (var clear in clears) events[clear.Address] = "clear";
        foreach (var store in stateStores) events[store.Address] = unchecked((int)store.Value.Offset) switch
        { 0 => "suspend-state", -1 => "resume-state", -2 => Reaches(consume.Address, store.Address) ? "complete-state" : "failed-state", _ => "unknown-state" };
        var failureStore = Only(stores.Where(s => IsThis(SsaSemantics.AddressParts(s.AddressValue).Root) && Equal(s.Value, fail.Arguments[1])));
        if (!Require(failureStore is not null, "builder 的同步异常存储不唯一")) return;
        events[failureStore!.Address] = "failure-store";
        foreach (var call in calls.Where(c => c.Name == "ThrowNullReference")) events[call.Address] = "null-throw";
        var allowedStores = stateStores.Concat(clears).Append(save).Append(failureStore).ToHashSet();
        Require(stores.Where(s => IsThis(SsaSemantics.AddressParts(s.AddressValue).Root)).All(allowedStores.Contains), "存在未归约的状态机写入");
        foreach (var store in stores.Where(s => !allowedStores.Contains(s)))
        {
            var root = SsaSemantics.AddressParts(store.AddressValue).Root;
            var local = root.Kind == "stack";
            var metadataFlag = root.Kind == "constant" && store.Value is { Kind: "constant", Width: 8, Offset: 1 } &&
                semantics.Program.Instructions.Any(i => i.Condition is { } c && Descendants(semantics.Resolve(c)).Any(t =>
                    t.Kind == "load" && t.Width == 8 && t.Inputs is [var address] && Equal(address, store.AddressValue)) &&
                    BranchReaches(i.Address, "taken", store.Address) != BranchReaches(i.Address, "not-taken", store.Address));
            var nativeException = root.Kind == "call-result" && calls.Any(c => c.Value == root.Name && c.Name == "CxxAllocateException") &&
                store.Value is { Kind: "load", Inputs: [{ Kind: "call-result" } wrapper] } && calls.Any(c => c.Value == wrapper.Name && c.Name == "CxxBeginCatch");
            Require(local || metadataFlag || nativeException, $"0x{store.Address:x}: 存在协议之外的内存写入");
        }
        var expected = new Dictionary<string, string[]>
        {
            ["entry"] = ["allocate", "restore"], ["allocate"] = ["construct"], ["construct"] = ["produce", "null-throw"],
            ["produce"] = ["status", "consume", "complete-state"], ["status"] = ["suspend-state", "consume", "complete-state"],
            ["restore"] = ["clear"], ["clear"] = ["resume-state"], ["resume-state"] = ["consume", "complete-state"],
            ["consume"] = ["complete-state"], ["complete-state"] = ["complete", "return"], ["complete"] = ["return"],
            ["suspend-state"] = ["save"], ["save"] = ["schedule"], ["schedule"] = ["return"],
            ["failed-state"] = ["fail", "failure-store"], ["fail"] = ["return"], ["failure-store"] = ["return"], ["null-throw"] = []
        };
        HashSet<string> Next(IEnumerable<ulong> initial)
        {
            var pending = new Stack<ulong>(initial); var seen = new HashSet<ulong>(); var found = new HashSet<string>();
            while (pending.TryPop(out var pc))
            {
                if (!seen.Add(pc)) continue;
                if (events.TryGetValue(pc, out var label)) { found.Add(label); continue; }
                var node = Flow.Nodes.Single(n => n.Instruction.Address == pc);
                if (node.Instruction.Mnemonic == "ret") found.Add("return");
                foreach (var edge in node.Edges.Where(e => e.Kind is "next" or "branch" or "normal-return" or "taken" or "not-taken"))
                    if (edge.Target is { } target) pending.Push(target);
            }
            return found;
        }
        Require(Next([Flow.Entry]).SetEquals(expected["entry"]), "入口事件图不符合协议");
        foreach (var (pc, label) in events)
        {
            var starts = Flow.Nodes.Single(n => n.Instruction.Address == pc).Edges.Where(e => e.Kind is "next" or "branch" or "normal-return" or "taken" or "not-taken").Select(e => e.Target).OfType<ulong>();
            var successors = Next(starts);
            Require(expected.TryGetValue(label, out var targets) && successors.SetEquals(targets), $"{label} 事件后继不符合协议：{string.Join(',', successors)}");
        }
        proofs.Add("projected native event graph matches allocation, await, suspension, resumption and builder exits; no extra state-machine stores");
    }
    private bool BranchReaches(ulong pc, string kind, ulong target) => Flow.Nodes.Single(n => n.Instruction.Address == pc).Edges
        .Any(e => e.Kind == kind && e.Target is { } start && Reaches(start, target));
    private bool NullGuard(SemanticTerm receiver, ulong call) => semantics.Program.Instructions.Any(i => i.Condition is { } condition &&
        semantics.Resolve(condition) is { Kind: "zero", Inputs: [var input] } && Equal(input, receiver) &&
        !BranchReaches(i.Address, "taken", call) && BranchReaches(i.Address, "not-taken", call));
    private bool Reaches(ulong start, ulong target)
    {
        var seen = new HashSet<ulong>(); var pending = new Stack<ulong>(); pending.Push(start);
        var nodes = Flow.Nodes.ToDictionary(n => n.Instruction.Address);
        while (pending.TryPop(out var pc))
        {
            if (pc == target) return true;
            if (!seen.Add(pc) || !nodes.TryGetValue(pc, out var node)) continue;
            foreach (var edge in node.Edges.Where(e => e.Kind is "next" or "normal-return" or "branch" or "taken" or "not-taken"))
                if (edge.Target is { } next) pending.Push(next);
        }
        return false;
    }
    private void ValidateExceptions(SsaManagedCall[] calls, params SsaManagedCall[] protocol)
    {
        var begin = Only(calls.Where(c => c.Name == "CxxBeginCatch"));
        var assignable = Only(calls.Where(c => c.Name == "IsAssignable"));
        Require(begin is not null && assignable is not null && assignable.Arguments[0] is { Kind: "metadata", Name: "System.Exception_TypeInfo" }, "未证明托管 System.Exception 捕获");
        if (begin is null) return;
        foreach (var call in protocol.Take(protocol.Length - 2))
            Require(Flow.Nodes.Single(n => n.Instruction.Address == call.Address).Edges.Any(e => e.Kind == "exception-dispatch" && e.Target is { } pad && Reaches(pad, begin.Address)), $"0x{call.Address:x}: await 主体异常未到达同一捕获入口");
        foreach (var call in protocol.TakeLast(2))
            Require(!Flow.Nodes.Single(n => n.Instruction.Address == call.Address).Edges.Any(e => e.Kind == "exception-dispatch"), $"0x{call.Address:x}: builder 出口位于主捕获区内");
        var exception = protocol[^1].Arguments[1];
        Require(exception is { Kind: "load", Inputs: [var wrapper] } && wrapper.Kind == "call-result" && wrapper.Name == begin.Value,
            "SetException 的参数并非来自捕获的托管异常");
        Require(assignable?.Arguments[1] is { Kind: "load", Inputs: [{ Kind: "load", Inputs: [var typedWrapper] }] } &&
            typedWrapper.Kind == "call-result" && typedWrapper.Name == begin.Value, "捕获类型检查未使用同一个异常对象");
        var rethrow = Only(calls.Where(c => c.Name == "CxxThrow"));
        var resume = Only(calls.Where(c => c.Name == "UnwindResume"));
        Require(rethrow is not null && resume is not null, "原生异常重抛/继续展开出口未保留");
        if (rethrow is null || resume is null || assignable is null) return;
        var filters = Flow.Nodes.SelectMany(n => n.Edges).Where(e => e.Kind == "exception-dispatch" && e.Region is not null)
            .SelectMany(e => e.Region!.Actions).Where(a => a.Kind == "typed-catch").Select(a => a.TypeInfo).Distinct().ToArray();
        Require(filters.Length == 1 && rethrow.Arguments[1] is { Kind: "constant" } rtti && (ulong)rtti.Offset == filters[0], "C++ RTTI 与 LSDA 捕获类型不一致");
        Require(semantics.Program.Instructions.Any(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero" } zero &&
            Descendants(zero).Any(v => v.Kind == "call-result" && v.Name == assignable.Value) && BranchReaches(i.Address, "taken", rethrow.Address) &&
            !BranchReaches(i.Address, "taken", protocol[^1].Address) && BranchReaches(i.Address, "not-taken", protocol[^1].Address)), "类型不匹配路径未重抛");
    }
    private string[]? BindSource(AsyncSource source, string stateType, SsaManagedCall work, long stateOffset)
    {
        var kickoff = Only(symbols.Methods.Values.SelectMany(v => v).Where(m => m.Name == source.Owner + "$$" + source.Name));
        if (!Require(kickoff is not null, "原始入口重载身份不唯一")) return null;
        var entry = lift(kickoff!);
        var invocation = Only(entry.Calls().Where(c => c.Name == method.Name));
        if (!Require(invocation is not null, "入口没有唯一调用当前状态机")) return null;
        var (frame, frameOffset) = SsaSemantics.AddressParts(invocation!.Arguments[0]);
        if (!Require(frame.Kind == "stack", "状态机入口存储不在已证明栈区域")) return null;
        var stores = entry.Stores().Where(s => s.Address < invocation.Address).ToArray();
        Require(stores.Any(s => SsaSemantics.AddressParts(s.AddressValue) is var a && Equal(a.Root, frame) && a.Offset == frameOffset + stateOffset && s.Value is { Kind: "constant", Width: 32, Offset: 4294967295 }), "入口没有初始化运行状态 -1");
        var arguments = new List<string>();
        foreach (var field in work.Arguments.Skip(1).SkipLast(1))
        {
            if (!Require(field is { Kind: "field", Inputs: [var root] } && IsThis(root), "await 参数不是已证明的状态机捕获值")) return null;
            var store = stores.LastOrDefault(s => SsaSemantics.AddressParts(s.AddressValue) is var a && Equal(a.Root, frame) && a.Offset == frameOffset + field.Offset && s.Value.Width == field.Width);
            if (!Require(store?.Value.Kind == "parameter", "入口没有对应的捕获参数写入")) return null;
            var index = Array.IndexOf(source.ParameterNames, store!.Value.Name);
            if (!Require(index >= 0, "捕获参数身份不在原始签名中")) return null;
            arguments.Add(source.ParameterNames[index]);
        }
        return arguments.ToArray();
    }
}
