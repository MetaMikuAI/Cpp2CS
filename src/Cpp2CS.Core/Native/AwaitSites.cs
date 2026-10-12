namespace Cpp2CS.Native;

public sealed record AwaitSite(ulong Schedule, int? State, long? StateOffset, long? AwaiterOffset,
    int AwaiterBytes, SemanticTerm? Awaiter, ulong[] Producers, ulong[] StatusCandidates,
    ulong[] ResultCandidates, string[] Problems)
{
    public UniTaskStorage? Storage { get; init; }
}
public sealed record AwaitSiteAnalysis(AwaitSite[] Sites, ulong[] UnresolvedCalls, string[] Problems)
{
    public string Scope => "suspension-dataflow; resume/exception/control-flow proof remains separate";
}

// 挂起点以调用身份区分；多个挂起点可以复用同一字段和同一本地槽。
public static class AwaitSites
{
    public static AwaitSiteAnalysis Recover(SsaSemantics semantics, Symbols symbols, HeaderLayout layouts)
    {
        var calls = semantics.Calls();
        var stores = semantics.Stores();
        var transparentCalls = calls.Where(c => c.Kind == "runtime" && c.Name == "WriteBarrier").Select(c => c.Address).ToHashSet();
        var states = stores.Where(s => AtThis(s.AddressValue) && s.Value is { Kind: "constant", Width: 32 })
            .GroupBy(s => SsaSemantics.AddressParts(s.AddressValue).Offset)
            .Where(g => g.Any(s => unchecked((int)s.Value.Offset) == -1) && g.Any(s => unchecked((int)s.Value.Offset) == -2)).ToArray();
        var stateOffset = states.Length == 1 ? (long?)states[0].Key : null;
        var sites = new List<AwaitSite>();
        foreach (var schedule in calls.Where(IsSchedule))
        {
            var problems = new List<string>();
            int? state = null;
            long? awaiterOffset = null;
            SemanticTerm? awaiter = null;
            var size = 0;
            if (stateOffset is null) problems.Add("状态字段不唯一");
            else
            {
                var reaching = ReachingStores(semantics.Program.Flow, stores, schedule.Address, states[0].First().AddressValue, 4, transparentCalls);
                if (reaching is [var store] && store is not null && store.Value is { Kind: "constant", Width: 32 } && unchecked((int)store.Value.Offset) >= 0)
                    state = unchecked((int)store.Value.Offset);
                else problems.Add("调度前的状态写入不唯一或未覆盖全部路径");
            }
            if (schedule.Arguments is [_, var local, var machine, _] && AtThis(machine) &&
                SsaSemantics.AddressParts(local).Root.Kind == "stack")
            {
                var candidates = stores.Where(s => AtThis(s.AddressValue) && s.Value.Width > 64 && s.Value.Width % 8 == 0)
                    .GroupBy(s => (SsaSemantics.AddressParts(s.AddressValue).Offset, s.Value.Width)).ToArray();
                var matches = new List<(long Offset, SemanticTerm Value)>();
                foreach (var candidate in candidates)
                {
                    var reaching = ReachingStores(semantics.Program.Flow, stores, schedule.Address, candidate.First().AddressValue, candidate.Key.Width / 8, transparentCalls);
                    if (reaching is not [var saved] || saved is null || saved.Value.Width != candidate.Key.Width) continue;
                    var value = semantics.LoadAtCall(schedule.Value, local, candidate.Key.Width / 8);
                    if (!HasUnknown(value) && value.Key == saved.Value.Key) matches.Add((candidate.Key.Offset, value));
                }
                if (matches.Count == 1) { awaiterOffset = matches[0].Offset; awaiter = matches[0].Value; size = awaiter.Width / 8; }
                else problems.Add("本地 awaiter 与状态机保存值没有唯一的完整对应");
            }
            else problems.Add("调度参数没有证明 ref awaiter/ref stateMachine");
            var producers = awaiter is null ? [] : Descendants(awaiter).Where(v => v.Kind == "call-result")
                .SelectMany(v => calls.Where(c => c.Value == v.Name).Select(c => c.Address)).Distinct().Order().ToArray();
            ulong[] MatchingCalls(string name) => awaiter is null ? [] : calls.Where(c => c.Kind == "interface" && c.Name.EndsWith("." + name) &&
                c.Arguments.Any(a => Descendants(a).Any(v => v.Key == awaiter.Key))).Select(c => c.Address).ToArray();
            sites.Add(new(schedule.Address, state, stateOffset, awaiterOffset, size, awaiter, producers,
                MatchingCalls("GetStatus"), MatchingCalls("GetResult"), problems.ToArray())
            { Storage = awaiter?.Type is { } type ? UniTaskStorage.Read(type, symbols, layouts) : null });
        }
        var duplicateStates = sites.Where(s => s.State is not null).GroupBy(s => (s.StateOffset, s.State))
            .Where(g => g.Count() > 1).Select(g => $"状态 {g.Key.State} 对应多个调度点，尚未证明其等价关系").ToArray();
        return new(sites.ToArray(), calls.Where(c => c.Kind == "indirect").Select(c => c.Address).ToArray(), duplicateStates);
    }
    public static bool IsSchedule(SsaManagedCall call) => call.Kind == "managed" &&
        call.Name.Split("$$") is [var owner, var member] &&
        (ManagedNames.SplitGeneric(owner).Name is "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder" or
            "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskVoidMethodBuilder" or
            "System.Runtime.CompilerServices.AsyncVoidMethodBuilder" or
            "System.Runtime.CompilerServices.AsyncTaskMethodBuilder" or
            "System.Runtime.CompilerServices.AsyncValueTaskMethodBuilder") &&
        (member.StartsWith("AwaitUnsafeOnCompleted<") || member.StartsWith("AwaitOnCompleted<"));
    private static bool AtThis(SemanticTerm value) => SsaSemantics.AddressParts(value).Root is { Kind: "parameter", Name: "__this", Offset: 0 };
    private static IEnumerable<SemanticTerm> Descendants(SemanticTerm value) => new[] { value }.Concat(value.Inputs.SelectMany(Descendants));
    private static bool HasUnknown(SemanticTerm value) => Descendants(value).Any(v => v.Kind is "unknown" or "ssa" or "clobber" or "memory-cycle");

    // 反向到达定义查询。未写入的入口路径、部分覆盖和别名不明都保留为未知。
    public static SsaManagedStore?[] ReachingStores(NativeControlFlow flow, SsaManagedStore[] stores,
        ulong before, SemanticTerm address, int bytes, ISet<ulong>? transparentCalls = null)
    {
        var predecessors = flow.Nodes.SelectMany(n => n.Edges).Where(e => e.Target is not null &&
            e.Kind is "next" or "branch" or "normal-return" or "taken" or "not-taken")
            .GroupBy(e => e.Target!.Value).ToDictionary(g => g.Key, g => g.Select(e => e.Source).ToArray());
        var writes = stores.GroupBy(s => s.Address).ToDictionary(g => g.Key, g => g.ToArray());
        var calls = flow.Nodes.Where(n => n.Instruction.Mnemonic is "bl" or "blr").Select(n => n.Instruction.Address).ToHashSet();
        var pending = new Stack<ulong>(predecessors.GetValueOrDefault(before, []));
        var seen = new HashSet<ulong>();
        var result = new HashSet<SsaManagedStore?>();
        var (root, offset) = SsaSemantics.AddressParts(address);
        if (before == flow.Entry) result.Add(null);
        while (pending.TryPop(out var pc))
        {
            if (!seen.Add(pc)) continue;
            if (calls.Contains(pc) && transparentCalls?.Contains(pc) != true) { result.Add(null); continue; }
            if (writes.GetValueOrDefault(pc, []).Any(s => SsaSemantics.AddressParts(s.AddressValue).Root is var other &&
                other.Key != root.Key && other.Kind != "stack")) { result.Add(null); continue; }
            var overlapping = writes.GetValueOrDefault(pc, []).Where(s =>
            {
                var (other, start) = SsaSemantics.AddressParts(s.AddressValue);
                return root.Key == other.Key && start < offset + bytes && offset < start + s.Value.Width / 8;
            }).ToArray();
            if (overlapping.Length != 0)
            {
                foreach (var store in overlapping)
                    result.Add(SsaSemantics.AddressParts(store.AddressValue).Offset == offset && store.Value.Width == bytes * 8 ? store : null);
                continue;
            }
            if (pc == flow.Entry) { result.Add(null); continue; }
            foreach (var predecessor in predecessors.GetValueOrDefault(pc, [])) pending.Push(predecessor);
        }
        return result.ToArray();
    }
}
