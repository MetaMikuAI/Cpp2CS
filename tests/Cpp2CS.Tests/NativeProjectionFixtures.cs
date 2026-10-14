using System.Text;
using System.Text.Json;
using Cpp2CS.Native;

public static class NativeProjectionFixtures
{
    public sealed record Case(ulong Address, int Offset, int Size, string Name, string ReturnType, string[] Types, string[] Names, bool Reject, bool Ssa = false);
    public sealed record Helper(ulong Address, string Kind, bool NoReturn);
    public static void Export(string configuration, string directory)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!;
        var cases = JsonSerializer.Deserialize<Case[]>(File.ReadAllText(Path.Combine(directory, "cases.json")))!;
        var code = File.ReadAllBytes(Path.Combine(directory, "cases.bin"));
        var symbols = new Symbols(Path.Combine(directory, "script.json"));
        var layouts = new HeaderLayout(Path.Combine(directory, "il2cpp.h"), inputs.Clang);
        var fixtureAssembly = Path.Combine(directory, "Managed.dll");
        using var managed = new ManagedNames(File.Exists(fixtureAssembly) ? fixtureAssembly : inputs.ManagedAssembly);
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
            var machine = new DecodedMethod(sample.Address, instructions, new(sample.Address, sample.Address + (ulong)sample.Size, null));
            LiftResult? body;
            string[] problems;
            if (sample.Ssa)
            {
                var abi = new NativeAbi(layouts, managed);
                var method = abi.Normalize(symbols.Unique(sample.Address)!);
                var flow = NativeControlFlow.Build(instructions, machine.Boundary, runtime.NoReturn);
                var ssa = new NativeSsa(flow, method, abi, symbols).Build();
                var semantics = new SsaSemantics(ssa, method, symbols, layouts, abi, image, runtime, new(image, decoder));
                var recovered = SsaBodyRecovery.Recover(new(method, machine, flow, ssa, semantics, symbols, [], [], []), managed, layouts, symbols);
                body = recovered.Body;
                problems = recovered.Problems;
            }
            else
            {
                body = new FunctionLifter(image, decoder, symbols, layouts, managed, runtime).Lift(machine);
                problems = body.Problems.ToArray();
            }
            if (sample.Reject != (problems.Length > 0)) throw new InvalidOperationException(sample.Name + ": " + string.Join("; ", problems));
            reports.Add(new { sample.Name, sample.Reject, Problems = problems });
            if (sample.Reject) continue;
            generated.Append("public static " + Display(sample.ReturnType) + " " + sample.Name + "(" +
                string.Join(", ", sample.Types.Zip(sample.Names, (type, name) => Display(type) + " " + name)) + ") ");
            generated.AppendLine(new SemanticWriter(symbols).Structured(ViewNormalizer.Normalize(body!), true));
        }
        generated.AppendLine("}");
        File.WriteAllText(Path.Combine(directory, "Recovered.cs"), generated.ToString());
        File.WriteAllText(Path.Combine(directory, "recovery.json"), JsonSerializer.Serialize(reports));
        Console.WriteLine($"PASS: {cases.Length} synthetic native functions recovered or explicitly rejected");
        string Display(string type) => layouts.ArrayElements(type) is { } elements ? Display(elements.Type) + "[]" : type switch
        {
            "void" => "void", "bool" => "bool", "Il2CppObject*" => "object", "System_String_o*" => "string", "int8_t" => "sbyte", "uint8_t" => "byte", "int16_t" => "short", "uint16_t" => "ushort",
            "int32_t" => "int", "uint32_t" => "uint", "int64_t" => "long", "uint64_t" => "ulong", "float" => "float", "double" => "double",
            _ when layouts.Shape(type).Kind is Cpp2CS.Abi.ShapeKind.Composite or Cpp2CS.Abi.ShapeKind.HomogeneousFloat => symbols.Display(type),
            _ => throw new InvalidOperationException(type)
        };
    }
}
