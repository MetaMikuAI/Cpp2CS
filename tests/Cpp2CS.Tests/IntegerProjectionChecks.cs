using System.Text;
using System.Text.Json;
using Cpp2CS.IR;
using Cpp2CS.Native;

public static class IntegerProjectionChecks
{
    public static void Run(Action<bool, string> check)
    {
        var word = new NativeValue(new InputBits("word", 32), "int32_t", new NameExpression("word"));
        var abi = word with { Bits = BitOps.Concat([word.Bits, new UnknownBits("upper", "ABI", 32)]) };
        check(IntegerProjection.Bits(abi) is null, "整数投影不把 ABI 未定义高位当成符号或零扩展");
        var zero = word with { Bits = BitOps.Concat([word.Bits, BitOps.Constant(0, 32)]) };
        check(IntegerProjection.Bits(zero) is OperationExpression { Operation: ValueOperation.IntegerCast, Type: "uint32_t" },
            "W 写入后的 64 位使用保留零扩展，即使原表达式为负 int");
        check(IntegerProjection.Bits(word with { Type = "Example_o*" }) is null && IntegerProjection.Bits(word with { Type = "float" }) is null,
            "引用和浮点值不能直接参与整数位运算");
        var wide = new NativeValue(new InputBits("wide", 64), "int64_t", new NameExpression("wide"));
        check(NativeValues.Slice(wide, 0, 32) is { Type: "int32_t", Expression: OperationExpression { Operation: ValueOperation.IntegerCast } },
            "整数低位切片在参数、返回及寄存器路径共用明确截断");
        check(NativeValues.Slice(new(BitOps.Constant(1, 64), "int64_t", new ConstantExpression(1)), 0, 8).Expression is ConstantExpression { Value: 1 },
            "窄常量保留常量身份及合法隐式转换，不提前变成有符号字节变量");
    }

    public sealed record Case(ulong Address, int Offset, int Size, string Name, string ReturnType, string[] Types, string[] Names, bool Reject);
    public static void Export(string configuration, string directory)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!;
        var cases = JsonSerializer.Deserialize<Case[]>(File.ReadAllText(Path.Combine(directory, "cases.json")))!;
        var code = File.ReadAllBytes(Path.Combine(directory, "cases.bin"));
        var symbols = new Symbols(Path.Combine(directory, "script.json"));
        var layouts = new HeaderLayout(Path.Combine(directory, "il2cpp.h"), inputs.Clang);
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var image = new ElfImage(inputs.Binary);
        var runtime = new RuntimeProfile(image);
        var generated = new StringBuilder("public static class Recovered\n{\n");
        var reports = new List<object>();
        foreach (var sample in cases)
        {
            var instructions = decoder.Decode(code.AsSpan(sample.Offset, sample.Size).ToArray(), sample.Address);
            var body = new FunctionLifter(image, decoder, symbols, layouts, managed, runtime).Lift(
                new DecodedMethod(sample.Address, instructions, new(sample.Address, sample.Address + (ulong)sample.Size, null)));
            if (sample.Reject != (body.Problems.Count > 0)) throw new InvalidOperationException(sample.Name + ": " + string.Join("; ", body.Problems));
            reports.Add(new { sample.Name, sample.Reject, body.Problems });
            if (sample.Reject) continue;
            generated.Append("public static " + Display(sample.ReturnType) + " " + sample.Name + "(" +
                string.Join(", ", sample.Types.Zip(sample.Names, (type, name) => Display(type) + " " + name)) + ") ");
            generated.AppendLine(new SemanticWriter(symbols).Structured(ViewNormalizer.Normalize(body), true));
        }
        generated.AppendLine("}");
        File.WriteAllText(Path.Combine(directory, "Recovered.cs"), generated.ToString());
        File.WriteAllText(Path.Combine(directory, "recovery.json"), JsonSerializer.Serialize(reports));
        Console.WriteLine($"PASS: {cases.Length} synthetic native functions recovered or explicitly rejected");
    }
    private static string Display(string type) => type switch
    { "int32_t" => "int", "uint32_t" => "uint", "int64_t" => "long", "uint64_t" => "ulong", _ => throw new InvalidOperationException(type) };
}
