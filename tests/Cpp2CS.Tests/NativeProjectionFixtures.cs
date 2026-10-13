using System.Text;
using System.Text.Json;
using Cpp2CS.Native;

public static class NativeProjectionFixtures
{
    public sealed record Case(ulong Address, int Offset, int Size, string Name, string ReturnType, string[] Types, string[] Names, bool Reject);
    public sealed record Helper(ulong Address, string Kind, bool NoReturn);
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
        var helpers = Path.Combine(directory, "helpers.json");
        if (File.Exists(helpers))
            foreach (var helper in JsonSerializer.Deserialize<Helper[]>(File.ReadAllText(helpers))!)
                runtime.Helpers.Add(helper.Address, new(helper.Kind, helper.NoReturn, "synthetic fixture helper contract"));
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
        string Display(string type) => layouts.ArrayElements(type) is { } elements ? Display(elements.Type) + "[]" : type switch
        {
            "void" => "void", "Il2CppObject*" => "object", "System_String_o*" => "string", "int8_t" => "sbyte", "uint8_t" => "byte", "int16_t" => "short", "uint16_t" => "ushort",
            "int32_t" => "int", "uint32_t" => "uint", "int64_t" => "long", "uint64_t" => "ulong", _ => throw new InvalidOperationException(type)
        };
    }
}
