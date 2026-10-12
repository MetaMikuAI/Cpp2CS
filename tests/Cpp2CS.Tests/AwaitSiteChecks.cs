using System.Text.Json;
using Cpp2CS.Native;

public static class AwaitSiteChecks
{
    public static void Run(Action<bool, string> check)
    {
        Instruction I(ulong pc, string op = "nop") => new(pc, op, "", [], false, false, "");
        NativeFlowNode Node(ulong pc, string op, params ulong[] successors) => new(I(pc, op), successors.Select(t => new NativeEdge(pc, t, "next")).ToArray(), true);
        var address = SsaSemantics.Term("parameter", 64, "__this");
        SsaManagedStore Store(ulong pc, long value) => new(pc, address, SsaSemantics.Number(value, 32));
        var first = Store(4, 0); var second = Store(12, 1);
        var flow = new NativeControlFlow(0, [Node(0, "nop", 4, 8), Node(4, "str", 16), Node(8, "nop", 12), Node(12, "str", 16), Node(16, "bl")], [], []);
        check(AwaitSites.ReachingStores(flow, [first, second], 16, address, 4).Length == 2, "不同路径的挂起状态不按地址顺序取最后一个");
        check(AwaitSites.ReachingStores(flow, [first], 16, address, 4).Contains(null), "未写入的入口路径显式保留未知");
        var loop = new NativeControlFlow(0, [Node(0, "nop", 4), Node(4, "str", 8), Node(8, "nop", 8, 16), Node(16, "bl")], [[8]], []);
        check(AwaitSites.ReachingStores(loop, [first], 16, address, 4) is [var found] && found == first, "循环中的到达定义查询终止且保留外部写入");
        var partial = new SsaManagedStore(8, SsaSemantics.Add(address, 2), SsaSemantics.Number(1, 16));
        check(AwaitSites.ReachingStores(loop, [first, partial], 16, address, 4) is [null], "部分覆盖不视为完整状态保存");
        var callFlow = loop with { Nodes = loop.Nodes.Select(n => n.Instruction.Address == 8 ? n with { Instruction = I(8, "bl") } : n).ToArray() };
        check(AwaitSites.ReachingStores(callFlow, [first], 16, address, 4) is [null], "未知调用阻断跨调用堆状态推断");
        check(AwaitSites.ReachingStores(callFlow, [first], 16, address, 4, new HashSet<ulong> { 8 }) is [var preserved] && preserved == first, "有副作用摘要的透明调用允许传播");
        var alias = new SsaManagedStore(8, SsaSemantics.Term("parameter", 64, "other"), SsaSemantics.Number(3, 32));
        check(AwaitSites.ReachingStores(loop, [first, alias], 16, address, 4) is [null], "未知别名写入阻断保存证明");
    }
    public static void Native(Action<bool, string> check, string path)
    {
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(path))!);
        var multi = session.Recover(0x55d684c);
        var sites = multi.Ssa!.AwaitSites!.Sites;
        check(sites.Length == 3 && sites.All(s => s.Problems.Length == 0), "真实三 await 样本提取三个独立挂起点");
        check(sites.Select(s => s.State).Order().SequenceEqual(new int?[] { 0, 1, 2 }) && sites.All(s => s.AwaiterOffset == 48), "三个状态复用同一 awaiter 字段仍保持独立身份");
        check(sites.All(s => s.Producers.Length == 1 && s.StatusCandidates.Length == 1 && s.ResultCandidates.Length == 1) &&
            sites.SelectMany(s => s.Producers).Distinct().Count() == 3, "三个 await 的生产者和接口消费候选不串值");
        var generic = session.Recover(0x55d4ad8);
        var work = generic.Ssa!.Calls.Single(c => c.Address == 0x55d4b64);
        check(work.Arguments[4] is { Kind: "field", Width: 32, Type: "float" }, "真实泛型 UniTask 调用的 float 参数来自 S0 字段值");
        var storage = generic.Ssa.AwaitSites!.Sites.Single().Storage;
        check(storage is { Bytes: 16, Source.Offset: 0, Token.Offset: 10, Result.Offset: 8, Result.Size: 1 }, "真实 UniTask<bool> 区分 source、内联 bool 和偏移 10 的 token");
        check(sites.All(s => s.Storage is { Token.Offset: 8, Result: null }), "非泛型 UniTask 使用偏移 8 的 token，不套用泛型布局");
        check(generic.Ssa.Calls.Where(c => c.Name == "EnsureClassMetadata").All(c => c.Arguments.Length == 1), "元数据类初始化 helper 仅包含签名定义的参数");
        check(generic.Ssa.Body is { CSharp: not null, Problems.Length: 0 } && generic.Ssa.Calls.All(c => c.Kind != "indirect"), "泛型接口上下文已绑定并通过完整协议检查");
        var voice = session.Recover(0x5b5e7b0);
        check(voice.Ssa!.AwaitSites!.Sites.Length == 2 && voice.Ssa.AwaitSites.Sites.All(s => s.Problems.Length == 0),
            "async void 中等待 UniTask 仍提取独立挂起点，不混淆 builder 与 awaitable");
        Directory.CreateDirectory("artifacts");
        File.WriteAllText("artifacts/multi-await-checks.json", JsonSerializer.Serialize(new { sites, genericSites = generic.Ssa.AwaitSites, voiceSites = voice.Ssa.AwaitSites,
            complete = new { branch = multi.Ssa.Body?.CSharp is not null, generic = generic.Ssa.Body?.CSharp is not null, voice = voice.Ssa.Body?.CSharp is not null } }, new JsonSerializerOptions { WriteIndented = true }));
    }
}
