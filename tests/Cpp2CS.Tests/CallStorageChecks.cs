using System.Text.Json;
using Cpp2CS.Native;

public static class CallStorageChecks
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
        var unusedTarget = symbols.Unique(0x58bc0a4)!;
        var unusedBoundary = UnwindBoundary.Read(image, unusedTarget.Address);
        var unusedCode = decoder.Decode(image.Read(unusedTarget.Address, (int)(unusedBoundary.End - unusedTarget.Address)), unusedTarget.Address);
        var unusedGraph = new NativeGraph(unusedCode, runtime.NoReturn, target => symbols.Unique(target) is not null || runtime.Helpers.ContainsKey(target));
        check(UnusedReceiver.Prove(unusedGraph, "x1", call => Arm64Calls.Inputs(call, symbols, abi, runtime)), "真实隐藏参数在读取前被完整覆盖，证明消费共享机器效果与 helper ABI");
        check(managed.BaseTypeOf("System.Object") is null, "无基类类型的 nil 元数据句柄返回空，不越界读取");
        var equivalents = new NativeBodyEquivalence(image, decoder);
        var owner = symbols.Unique(0x58bbcb8)!;
        var enumerator = symbols.Unique(0x88e3288)!;
        var moveNext = symbols.Unique(0x796d25c)!;
        check(abi.Classify(enumerator) is { Return.Indirect: true, Return.Shape.Size: 24 }, "真实枚举器使用 24 字节间接返回");

        SsaSemantics Sample(NativeMethod target, long offset, string operation, bool unknownBuffer = false, bool overwrite = false)
        {
            var values = new List<SsaValue>
            {
                new("frame", "stack-address", 64, []), new("offset", "constant", 64, [], Immediate: offset),
                new("address", "add", 64, ["frame", "offset"]), new("zero", "constant", 64, []),
                new("unknown", "unknown", 64, []), new("target", "constant", 64, [], Immediate: (long)target.Address),
                new("entry", "memory", 0, []), new("seed", "store", 0, ["entry", "address", "zero"]),
                new("saved", "store", 0, ["seed", "beyond", "one"]),
                new("call", "call", 192, ["target", "saved", target == moveNext ? "address" : "zero", "zero", "zero", "zero", "zero", "zero", "zero", "zero", unknownBuffer ? "unknown" : "address", "zero", "zero", "zero", "zero", "zero", "zero", "zero", "zero"]),
                new("after", operation, 0, ["saved", "call"]),
                new("one", "constant", 8, [], Immediate: 1), new("overwrite", "store", 0, ["after", "address", "one"]),
                new("full", "load", 192, [overwrite ? "overwrite" : "after", "address"]),
                new("byte", "load", 8, [overwrite ? "overwrite" : "after", "address"]),
                new("beyond", "add", 64, ["address", "size"]), new("size", "constant", 64, [], Immediate: 24),
                new("outside", "load", 8, ["after", "beyond"])
            };
            var program = new NativeSsaProgram(new(0, [], [], []), values.ToArray(), [], []);
            return new(program, owner, symbols, layouts, abi, image, runtime, equivalents);
        }
        foreach (var offset in new long[] { -160, -64, 0, 48 })
        {
            var normal = Sample(enumerator, offset, "call-memory");
            check(normal.Resolve("full") is { Kind: "call-result", Name: "call", Width: 192 }, "返回缓冲的全部字节来自同一调用，不依赖固定偏移");
            check(normal.Resolve("outside") is { Kind: "constant", Offset: 1 }, "返回值不能覆盖缓冲范围之外的已知哨兵值");
            check(SsaSemantics.Contains(Sample(enumerator, offset, "exception-memory").Resolve("byte"), "unknown"), "异常返回不能承诺返回结构体字节或沿用旧值");
            check(SsaSemantics.Contains(Sample(enumerator, offset, "call-memory", unknownBuffer: true).Resolve("byte"), "unknown"), "未知 X8 不能保留旧栈值");
            var partial = Sample(enumerator, offset, "call-memory", overwrite: true);
            check(partial.Resolve("byte") is { Kind: "constant", Offset: 1 }, "返回后的部分写入覆盖相应字节");
            check(partial.Resolve("full").Kind == "compose", "部分覆盖不合并为完整调用返回值");
            check(Sample(moveNext, offset, "call-memory").Resolve("full") is { Kind: "call-storage", Name: "call" }, "ref 值类型接收者使用调用后的存储身份");
            check(SsaSemantics.Contains(Sample(moveNext, offset, "exception-memory").Resolve("full"), "unknown"), "ref 调用抛异常时不能生成完整的新值");
        }

        var boundary = UnwindBoundary.Read(image, owner.Address);
        var code = decoder.Decode(image.Read(owner.Address, (int)(boundary.End - owner.Address)), owner.Address);
        var flow = NativeControlFlow.Build(code, boundary, runtime.NoReturn);
        var actual = new SsaSemantics(new NativeSsa(flow, owner, abi, symbols).Build(), owner, symbols, layouts, abi, image, runtime, equivalents);
        var copied = actual.Stores().Single(s => s.Address == 0x58bbebc).Value;
        check(!SsaSemantics.Contains(copied, "unknown") && SsaSemantics.Contains(copied, "call-result"), "返回缓冲复制保留调用结果来源");
        var add = actual.Calls().Single(c => c.Address == 0x58bbeec);
        check(!SsaSemantics.Contains(add.Arguments[1], "unknown") && SsaSemantics.Contains(add.Arguments[1], "call-storage"), "真实 Current 来源保留 MoveNext 后的值类型存储");
        check(actual.CallStorages().Any(s => s.Call == "call_58bbeb0" && s.Kind == "indirect-return"), "真实间接返回存储效果可导出");
        check(flow.Nodes.SelectMany(n => n.Edges).Any(e => e.Kind.StartsWith("exception-")), "存储分析保留异常边");
        var rethrow = actual.Calls().Where(c => c.Name == "RethrowException").ToArray();
        check(rethrow.Length == 2 && rethrow.All(c => c.Arguments.Length == 1), "重抛 helper 的签名包含一个参数");
        check(rethrow.All(c => flow.Nodes.Single(n => n.Instruction.Address == c.Address).Edges.All(e => e.Kind != "normal-return")), "重抛异常不能落入下一个处理块");
        check(flow.Nodes.SelectMany(n => n.Edges).Where(e => e.Region?.Actions.Any(a => a.Kind == "cleanup") == true).All(e => e.Kind != "unmatched-exception-unwind"), "真实清理区域不存在绕过 Dispose 的虚构展开边");

        var rotated = new FunctionLifter(image, decoder, symbols, layouts, managed, runtime).Lift(0x57921fc);
        var addition = rotated.Blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>().Single(c => c.Address == 0x5792334);
        var unknownStorage = false;
        SourceTree.Map(addition.Arguments[1], value => { unknownStorage |= value is UnknownExpression; return value; });
        check(rotated.Problems.Count > 0 && unknownStorage, "未证明的真实栈构造调用不能继续使用调用前的零值");
    }
}
