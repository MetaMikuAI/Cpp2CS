using System.Text.Json;
using Cpp2CS.Native;

public static class SsaConstructionChecks
{
    public static void Native(Action<bool, string> check, string configuration)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!;
        var symbols = new Symbols(inputs.Symbols);
        var layouts = new HeaderLayout(inputs.Header, inputs.Clang);
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var abi = new NativeAbi(layouts, managed);
        NativeMethod method = new(0x1000, "Fixture$$Identity", "uint64_t", [new("uint64_t", "value")], "");
        NativeSsaProgram Build(Instruction[] instructions, NativeFlowNode[]? nodes = null) => new NativeSsa(
            nodes is null ? NativeControlFlow.Build(instructions, new(method.Address, instructions[^1].Address + 4, null), _ => false) :
                new(method.Address, nodes, [], []), method, abi, symbols).Build();
        static SsaValue Resolve(NativeSsaProgram program, string id)
        {
            var values = program.Values.ToDictionary(v => v.Id);
            var seen = new HashSet<string>();
            while (values[id] is { Operation: "alias", Inputs: [var next] } && seen.Add(id)) id = next;
            return values[id];
        }
        void Complete(NativeSsaProgram program)
        {
            var ids = program.Values.Select(v => v.Id).ToHashSet();
            check(program.Values.All(v => v.Operation != "pending" && (v.Operation != "phi" || v.Incoming is not null)), "SSA 构造完成后没有未填充的值");
            check(program.Values.All(v => v.Inputs.Concat(v.Incoming?.Select(i => i.Value) ?? []).All(ids.Contains)), "SSA 所有引用都有对应值定义");
        }

        // 长直线图单独检验 SSA，不把其他图算法的调用栈混入测试。
        var bytes = Enumerable.Repeat(Convert.FromHexString("1F2003D5"), 4095).SelectMany(b => b).Concat(Convert.FromHexString("C0035FD6")).ToArray();
        var code = decoder.Decode(bytes, method.Address);
        var linear = code.Select(i => new NativeFlowNode(i, [new(i.Address, i.Mnemonic == "ret" ? null : i.Address + 4,
            i.Mnemonic == "ret" ? "return" : "next")], true)).ToArray();
        var longProgram = Build(code, linear);
        Complete(longProgram);
        var returned = longProgram.Values.Single(v => v.Operation == "return");
        check(Resolve(longProgram, returned.Inputs[0]).Id == "arg_0" && Resolve(longProgram, returned.Inputs[1]).Operation == "unknown",
            "4096 条指令的前驱链仍返回入口参数，未定义的第二寄存器保持未知");

        // cbz x1, exit; add x0, x0, #1; sub x1, x1, #1; b entry; ret
        code = decoder.Decode(Convert.FromHexString("810000B400040091210400D1FDFFFF17C0035FD6"), method.Address);
        method = method with { Parameters = [new("uint64_t", "value"), new("uint64_t", "count")] };
        var loop = Build(code);
        Complete(loop);
        var carried = Resolve(loop, loop.Values.Single(v => v.Operation == "return").Inputs[0]);
        check(carried.Operation == "phi" && carried.Incoming is { Length: 2 } &&
            carried.Incoming.Any(i => Resolve(loop, i.Value).Id == "arg_0") &&
            carried.Incoming.Any(i => Resolve(loop, i.Value).Operation == "add"), "循环合流同时保留入口参数和回边运算");

        // 未知调用的正常结果与异常入口不能共享返回值。
        code = decoder.Decode(Convert.FromHexString("00003FD6C0035FD6C0035FD6"), method.Address);
        var call = Build(code,
        [
            new(code[0], [new(0x1000, 0x1004, "normal-return"), new(0x1000, 0x1008, "exception-cleanup")], true),
            new(code[1], [new(0x1004, null, "return")], true),
            new(code[2], [new(0x1008, null, "return")], true)
        ]);
        Complete(call);
        var normalReturn = call.Values.Single(v => v.Id == "return_1004");
        var exceptionalReturn = call.Values.Single(v => v.Id == "return_1008");
        check(Resolve(call, normalReturn.Inputs[0]).Operation == "clobber" &&
            Resolve(call, exceptionalReturn.Inputs[0]).Operation == "exception-object" &&
            Resolve(call, exceptionalReturn.Inputs[1]).Operation == "exception-selector", "正常调用破坏与异常对象、选择器分别建值");

        var image = new ElfImage(inputs.Binary);
        var reader = new Arm64MethodReader(image, decoder, symbols);
        var runtime = new RuntimeProfile(image);
        var machine = reader.Read(0x5be3c00);
        method = symbols.Unique(machine.Address)!;
        var real = new NativeSsa(NativeControlFlow.Build(machine.Instructions, machine.Boundary, runtime.NoReturn), method, abi, symbols).Build();
        Complete(real);
        check(real.Instructions.Length > 0, "真实长方法完成 SSA 构图");
        Console.WriteLine($"SSA construction: {longProgram.Instructions.Length} linear instructions; {real.Instructions.Length} real instructions");
    }
}
