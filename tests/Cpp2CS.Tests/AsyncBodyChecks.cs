using System.Text.Json;
using Cpp2CS.Native;

public static class AsyncBodyChecks
{
    public static void Run(Action<bool, string> check, string path)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(path))!;
        var symbols = new Symbols(inputs.Symbols);
        var layouts = new HeaderLayout(inputs.Header, inputs.Clang);
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var image = new ElfImage(inputs.Binary);
        var runtime = new RuntimeProfile(image);
        var equivalents = new NativeBodyEquivalence(image, decoder);
        var abi = new NativeAbi(layouts, managed);
        var cache = new Dictionary<ulong, SsaSemantics>();
        SsaSemantics Lift(NativeMethod source)
        {
            if (cache.TryGetValue(source.Address, out var cached)) return cached;
            source = abi.Normalize(source);
            var boundary = UnwindBoundary.Read(image, source.Address);
            var flow = NativeControlFlow.Build(decoder.Decode(image.Read(source.Address, (int)(boundary.End - source.Address)), source.Address), boundary, runtime.NoReturn);
            return cache[source.Address] = new(new NativeSsa(flow, source, abi, symbols).Build(), source, symbols, layouts, abi, image, runtime, equivalents);
        }
        var outcomes = new List<object>();
        foreach (var address in new ulong[] { 0x55d684c, 0x55d4ad8, 0x5bea518 })
        {
            var method = abi.Normalize(symbols.Unique(address)!);
            var program = JsonSerializer.Deserialize<NativeSsaProgram>(File.ReadAllText($"artifacts/recovered/0x{address:x}.ssa.json"))!;
            SsaSemantics Semantics(NativeSsaProgram candidate)
            {
                var semantics = new SsaSemantics(candidate, method, symbols, layouts, abi, image, runtime, equivalents);
                VirtualDispatch.Recover(semantics, symbols, layouts, managed);
                new InterfaceDispatch(semantics, layouts, managed, runtime).Recover();
                return semantics;
            }
            AsyncBody? Recover(NativeSsaProgram candidate) => new AsyncBodyRecovery(Semantics(candidate), method, managed, layouts, symbols, Lift).Recover();
            var baseline = Recover(program)!;
            check(baseline is { CSharp: not null, Problems.Length: 0 }, $"0x{address:x}: 完整 async 输出：{string.Join("; ", baseline.Problems)}");
            var semantics = Semantics(program);
            var reads = program.Values.Where(v => v.Operation == "load").ToDictionary(v => v.Id);
            var snapshots = baseline.Projection!.Blocks.Values.SelectMany(b => b.Statements).OfType<AssignStatement>().Where(s => reads.ContainsKey(s.Name)).ToArray();
            if (address != 0x5bea518) check(snapshots.Length > 0, "含业务字段的真实 async 方法生成读取快照");
            check(snapshots.All(s => s.Address == reads[s.Name].Address), "async 业务字段快照保留原生读取位置");
            var sites = AwaitSites.Recover(semantics, symbols, layouts).Sites;
            check(semantics.Calls().All(c => c.Kind != "indirect"), "接口和虚调用全部解析");
            void Reject(string name, NativeSsaProgram candidate)
            {
                var result = Recover(candidate);
                check(result is { CSharp: null, Problems.Length: > 0 }, name);
                outcomes.Add(new { address = $"0x{address:x}", name, rejected = result?.CSharp is null, reasons = result?.Problems });
            }
            NativeSsaProgram Change(Func<SsaValue, SsaValue> transform, params SsaValue[] extra) => program with { Values = program.Values.Select(transform).Concat(extra).ToArray() };
            NativeSsaProgram Edges(ulong at, Func<NativeEdge, NativeEdge> transform) => program with
            { Flow = program.Flow with { Nodes = program.Flow.Nodes.Select(n => n.Instruction.Address == at ? n with { Edges = n.Edges.Select(transform).ToArray() } : n).ToArray() } };
            if (snapshots.FirstOrDefault() is { } snapshot)
                Reject("仍被使用的业务读取落入已收缩协议区时拒绝", Change(v => v.Id == snapshot.Name ? v with { Address = sites[0].Schedule } : v));
            Reject("不支持的 SSA 操作不会被协议遮蔽", program with { Problems = ["unsupported test operation"] });
            IEnumerable<SemanticTerm> Terms(SemanticTerm term) => new[] { term }.Concat(term.Inputs.SelectMany(Terms));
            var stateBranch = program.Instructions.First(i => i.Condition is { } c && Terms(semantics.Resolve(c)).Any(t =>
                t is { Kind: "field", Width: 32, Inputs: [{ Kind: "parameter", Name: "__this" }] } && t.Offset == sites[0].StateOffset));
            Reject("恢复状态分支反转时拒绝", Change(v => v.Id == stateBranch.Condition ? v with { Operation = v.Operation switch { "zero" => "nonzero", "nonzero" => "zero", "b.eq" => "b.ne", "b.ne" => "b.eq", _ => "test-unsupported" } } : v));
            var source = semantics.Calls().Single(c => c.Address == sites[0].StatusCandidates[0]).Arguments[0];
            var sourceGuard = program.Instructions.First(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero", Inputs: [var value] } && value.Key == source.Key);
            Reject("source 空路径反转时拒绝", Change(v => v.Id == sourceGuard.Condition ? v with { Operation = "nonzero" } : v));
            var poison = new SsaValue("test_poison", "constant", 64, [], Immediate: 1);
            var clear = semantics.Stores().First(s => s.Value is { Kind: "constant", Width: 64, Offset: 0 } &&
                SsaSemantics.AddressParts(s.AddressValue) is var a && a.Root is { Kind: "parameter", Name: "__this" } && a.Offset == sites[0].AwaiterOffset);
            Reject("awaiter 恢复未完整清空时拒绝", Change(v => v.Operation == "store" && v.Address == clear.Address ? v with { Inputs = [v.Inputs[0],v.Inputs[1],poison.Id] } : v, poison));
            var stackStore = program.Values.First(v => v.Operation == "store");
            Reject("额外状态机写入时拒绝", Change(v => v.Id == stackStore.Id ? v with { Inputs = [v.Inputs[0],"arg_0",v.Inputs[2]] } : v));
            foreach (var site in sites)
            {
                var status = semantics.Calls().Single(c => c.Address == site.StatusCandidates[0]);
                var condition = program.Instructions.Single(i => i.Condition is { } c && semantics.Resolve(c) is { Kind: "zero" or "nonzero", Inputs: [var input] } &&
                    input.Key == SsaSemantics.Slice(semantics.Resolve(status.Value),0,32).Key);
                Reject($"状态 {site.State} Pending 分支反转时拒绝", Change(v => v.Id == condition.Condition ? v with { Operation = v.Operation == "zero" ? "nonzero" : "zero" } : v));
                Reject($"状态 {site.State} 调度后继续业务时拒绝", Edges(site.Schedule, e => e.Kind == "normal-return" ? e with { Target = site.Producers[0] } : e));
                var consume = semantics.Calls().Single(c => c.Address == site.ResultCandidates[0]);
                var target = program.Values.Single(v => v.Id == consume.Value);
                Reject($"状态 {site.State} GetResult token 丢失时拒绝", Change(v => v.Id == target.Id ? v with { Inputs = v.Inputs.Select((x,i) => i == 3 ? poison.Id : x).ToArray() } : v, poison));
            }
            var work = sites[0].Producers[0];
            Reject("业务调用脱离异常捕获区时拒绝", Edges(work, e => e.Kind == "exception-dispatch" ? e with { Kind = "exception-unwind", Target = null } : e));
            if (address == 0x5bea518)
            {
                var call = program.Values.Single(v => v.Id == "call_5bea5c4");
                Reject("虚调用接收者与 vtable 对象不一致时拒绝", Change(v => v.Id == call.Id ? v with { Inputs = v.Inputs.Select((x,i) => i == 2 ? "arg_0" : x).ToArray() } : v));
                Reject("虚调用 MethodInfo 不配对时拒绝", Change(v => v.Id == call.Id ? v with { Inputs = v.Inputs.Select((x,i) => i == 3 ? "arg_0" : x).ToArray() } : v));
            }
        }
        check(managed.InterfaceSlot("Cysharp.Threading.Tasks.IUniTaskSource<System.Boolean>", 0)?.ReturnType == "System.Boolean", "泛型接口槽使用绑定后的 bool 返回类型");
        check(managed.InterfaceSlot("Cysharp.Threading.Tasks.IUniTaskSource", 0)?.ReturnType != "System.Boolean", "同名不同泛型元数不混淆");
        File.WriteAllText("artifacts/multi-async-mutations.json", JsonSerializer.Serialize(new { baseline = "passed", cases = outcomes }, new JsonSerializerOptions { WriteIndented = true }));
    }
}
