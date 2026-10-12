using System.Text.Json;
using Cpp2CS.Native;

public static class SsaRecoveryChecks
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
        var method = abi.Normalize(symbols.Unique(0x55d9650)!);
        var program = JsonSerializer.Deserialize<NativeSsaProgram>(File.ReadAllText("artifacts/recovered/0x55d9650.ssa.json"))!;
        SsaSemantics Lift(NativeMethod source)
        {
            source = abi.Normalize(source);
            var boundary = UnwindBoundary.Read(image, source.Address);
            var code = decoder.Decode(image.Read(source.Address, (int)(boundary.End - source.Address)), source.Address);
            var flow = NativeControlFlow.Build(code, boundary, runtime.NoReturn);
            return new(new NativeSsa(flow, source, abi, symbols).Build(), source, symbols, layouts, abi, image, runtime, equivalents);
        }
        AsyncProtocol? Recover(NativeSsaProgram candidate)
        {
            var semantics = new SsaSemantics(candidate, method, symbols, layouts, abi, image, runtime, equivalents);
            new InterfaceDispatch(semantics, layouts, managed, runtime).Recover();
            return new AsyncRecovery(semantics, method, managed, layouts, symbols, Lift).Recover();
        }
        var baseline = Recover(program)!;
        check(baseline.CSharp is not null && baseline.Problems.Length == 0, "真实 SSA 能恢复完整 async 输出");
        var cases = new List<object>();
        void Reject(string name, NativeSsaProgram candidate)
        {
            var result = Recover(candidate);
            check(result is { CSharp: null, Problems.Length: > 0 }, name);
            cases.Add(new { name, rejected = result?.CSharp is null, reasons = result?.Problems });
        }
        NativeSsaProgram Change(Func<SsaValue, SsaValue> transform, params SsaValue[] extra) => program with { Values = program.Values.Select(transform).Concat(extra).ToArray() };
        var setup = program.Values.Single(v => v.Id == "call_55d96d8");
        Reject("第二返回寄存器误取第一寄存器时拒绝 await", Change(v => v.Operation == "slice" && v.Inputs.SequenceEqual([setup.Id]) && v.Immediate == 64 ? v with { Immediate = 0 } : v));
        Reject("取消参数误换成 Transform 时拒绝 await", Change(v => v.Id == setup.Id ? v with { Inputs = v.Inputs.Select((x, n) => n == 6 ? v.Inputs[5] : x).ToArray() } : v));
        var poison = new SsaValue("test_nonzero", "constant", 64, [], Immediate: 1);
        Reject("恢复后只清一半 awaiter 时拒绝 await", Change(v => v.Id == "store_55d97c4_1" ? v with { Inputs = [v.Inputs[0], v.Inputs[1], poison.Id] } : v, poison));
        Reject("挂起条件反转时拒绝 await", Change(v => v.Id == "condition_55d97ec" ? v with { Operation = "nonzero" } : v));
        Reject("source 空引用分支反转时拒绝 await", Change(v => v.Id == "condition_55d9768" ? v with { Operation = "nonzero" } : v));
        Reject("接口循环计数递增时拒绝 await", Change(v => v.Id == "value_55d979c" ? v with { Operation = "add" } : v));
        Reject("额外状态机字段写入时拒绝 await", Change(v => v.Id == "store_55d9698_0" ? v with { Inputs = [v.Inputs[0], "arg_0", v.Inputs[2]] } : v));
        Reject("额外堆对象写入时拒绝 await", Change(v => v.Id == "store_55d9730_0" ? v with { Inputs = [v.Inputs[0], "out_55d96b4_x0", v.Inputs[2]] } : v));
        var wrongSlot = new SsaValue("test_slot", "constant", 64, [], Immediate: 3);
        Reject("接口快慢路径槽不一致时拒绝 await", Change(v => v.Id == "value_55d9868" ? v with { Inputs = [v.Inputs[0], wrongSlot.Id] } : v, wrongSlot));
        var caught = program.Flow.Nodes.Single(n => n.Instruction.Address == 0x55d9880).Edges.Single(e => e.Kind == "exception-dispatch");
        Reject("SetResult 被错误放入主捕获区时拒绝 await", program with
        {
            Flow = program.Flow with { Nodes = program.Flow.Nodes.Select(n => n.Instruction.Address == baseline.Complete ? n with
                { Edges = n.Edges.Append(caught with { Source = baseline.Complete }).ToArray() } : n).ToArray() }
        });
        Reject("接口循环的零计数出口错误时拒绝 await", program with
        {
            Flow = program.Flow with { Nodes = program.Flow.Nodes.Select(n => n.Instruction.Address == 0x55d9784 ? n with
                { Edges = n.Edges.Select(e => e.Kind == "taken" ? e with { Target = 0x55d9790 } : e).ToArray() } : n).ToArray() }
        });
        Reject("未实现机器操作不会被 async 模板遮蔽", program with { Problems = ["synthetic unsupported operation"] });
        File.WriteAllText("artifacts/async-mutation-checks.json", JsonSerializer.Serialize(new { baseline = "passed", cases }, new JsonSerializerOptions { WriteIndented = true }));
    }
}
