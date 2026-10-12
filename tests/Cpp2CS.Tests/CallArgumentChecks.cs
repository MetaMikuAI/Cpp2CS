using System.Text.Json;
using Cpp2CS.Abi;
using Cpp2CS.Native;

public static class CallArgumentChecks
{
    public static void Native(Action<bool, string> check, string path)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(path))!;
        var symbols = new Symbols(inputs.Symbols);
        var layouts = new HeaderLayout(inputs.Header, inputs.Clang);
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var image = new ElfImage(inputs.Binary);
        var runtime = new RuntimeProfile(image);
        var abi = new NativeAbi(layouts, managed);
        var method = abi.Normalize(symbols.Unique(0x59b3024)!);
        var boundary = UnwindBoundary.Read(image, method.Address);
        var instructions = decoder.Decode(image.Read(method.Address, (int)(boundary.End - method.Address)), method.Address);
        var flow = NativeControlFlow.Build(instructions, boundary, runtime.NoReturn);
        var program = new NativeSsa(flow, method, abi, symbols).Build();
        SsaSemantics Semantics(NativeSsaProgram source) => new(source, method, symbols, layouts, abi, image, runtime, new(image, decoder));
        var semantics = Semantics(program);
        var interfaces = new InterfaceDispatch(semantics, layouts, managed, runtime).Recover();
        var calls = semantics.Calls();
        check(interfaces.Length == 4 && calls.All(c => c.Kind != "indirect"), "真实 async 的四个接口调用均有槽位与 MethodInfo 证明");
        var execute = calls.Single(c => c.Address == 0x59b31a8);
        check(execute.Arguments.Length == 10 && execute.Arguments[8] is { Kind: "constant", Offset: 0 }, "真实 API Execute 的第一个栈参数保留为空");
        check(execute.Arguments[9] is { Kind: "metadata", Name: var name } && name.Contains("UserMysekaiSiteBulkHarvestRequest, UserMysekaiSiteBulkHarvestResponse"), "MethodInfo 从调用前 SP+8 恢复具体泛型实参");
        check(execute.Arguments.All(a => !SsaSemantics.Contains(a, "unknown")), "真实 API Execute 没有丢失栈参数");
        var complete = calls.Single(c => c.Address == 0x59b34a4);
        check(complete is { Kind: "interface", Arguments.Length: 2 } && complete.Arguments[1].Width == 128, "SetResult 的双寄存器结构体重组为一个 128 位逻辑参数");
        var definition = managed.InterfaceSlot(interfaces.Single(i => i.Address == complete.Address).Interface, 2)!;
        var layout = semantics.InterfaceLayout(definition)!;
        check(layout.Arguments[1].Pieces.Count == 2 && layout.Arguments[^1].Pieces[0].Location is RegisterLocation { Name: "X3" }, "MethodInfo 位置由结构体 ABI 决定为 X3");
        check(semantics.InterfaceLayout(new("Synthetic", 0, "M", "System.Void", ["Missing.Type"])) is null, "未知托管类型不猜测接口 ABI");
        var floating = semantics.InterfaceLayout(new("Synthetic", 0, "M", "System.Single", ["System.Single"]))!;
        check(floating.Arguments[1].Pieces[0].Location is RegisterLocation { Name: "V0" } && floating.Arguments[^1].Pieces[0].Location is RegisterLocation { Name: "X1" }, "浮点接口参数使用 V0，MethodInfo 不按参数个数猜测 X2");
        NativeSsaProgram Mutate(Func<SsaValue, SsaValue> change) => program with { Values = program.Values.Select(change).Append(new("test_unknown", "unknown", 64, [])).ToArray() };
        var wrongInfo = Semantics(Mutate(v => v.Id == complete.Value ? v with { Inputs = v.Inputs.Select((id, n) => n == 5 ? "test_unknown" : id).ToArray() } : v));
        check(new InterfaceDispatch(wrongInfo, layouts, managed, runtime).Recover().All(i => i.Address != complete.Address), "破坏 X3 MethodInfo 时拒绝接口归约");
        var unknownSp = Semantics(Mutate(v => v.Id == execute.Value ? v with { Inputs = v.Inputs.Select((id, n) => n == 19 ? "test_unknown" : id).ToArray() } : v));
        check(unknownSp.Calls().Single(c => c.Address == execute.Address).Arguments[9].Kind != "metadata", "未知调用前 SP 不沿用具体 MethodInfo");

        foreach (var offset in new long[] { -160, -32, 0, 48 })
        {
            var values = new SsaValue[]
            {
                new("frame", "stack-address", 64, []), new("offset", "constant", 64, [], Immediate: offset),
                new("sp", "add", 64, ["frame", "offset"]), new("eight", "constant", 64, [], Immediate: 8),
                new("second", "add", 64, ["sp", "eight"]), new("before", "constant", 64, [], Immediate: 42),
                new("after", "constant", 64, [], Immediate: 99), new("zero", "constant", 64, []), new("memory", "memory", 0, []),
                new("stored", "store", 0, ["memory", "second", "before"]), new("later", "store", 0, ["stored", "second", "after"]),
                new("call", "call", 0, ["zero", "stored", .. Enumerable.Repeat("zero", 17), "sp"])
            };
            var sample = Semantics(new(new(0, [], [], []), values, [], []));
            var arg = new AbiValue(AbiShape.Integer(), new([new(new StackLocation(8), 0, 8)]));
            check(sample.AbiArgument("call", arg) is { Kind: "constant", Offset: 42 }, "栈参数使用调用前 SP 和内存，不受后续覆盖影响：" + offset);
        }
    }
}
