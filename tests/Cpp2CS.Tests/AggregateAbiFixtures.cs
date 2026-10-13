using System.Text.Json;
using Cpp2CS.Abi;
using Cpp2CS.Model;
using Cpp2CS.Native;

public static class AggregateAbiFixtures
{
    public sealed record Sample(string Type, int Prefix, bool Reject);
    public static void Export(string configuration, string directory)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!;
        var layouts = new HeaderLayout(Path.Combine(directory, "types.h"), inputs.Clang);
        var samples = JsonSerializer.Deserialize<Sample[]>(File.ReadAllText(Path.Combine(directory, "cases.json")))!;
        var evidence = new Evidence(EvidenceKind.Derived, "AArch64 header layout fixture");
        object Value(AbiValue value) => new
        {
            value.Shape, value.Indirect,
            Pieces = value.Pieces.Select(p => new { p.ValueOffset, p.Size, Register = (p.Location as RegisterLocation)?.Name,
                StackOffset = (p.Location as StackLocation)?.Offset }).ToArray()
        };
        object Layout(CallLayout layout) => new { Arguments = layout.Arguments.Select(Value).ToArray(), Return = Value(layout.Return), layout.StackBytes };
        var reports = new List<object>();
        foreach (var sample in samples)
        {
            var shape = layouts.Shape(sample.Type);
            AbiShape[] arguments = [.. Enumerable.Repeat(AbiShape.Integer(), sample.Prefix), shape, AbiShape.Integer()];
            var checksum = Aapcs64.Classify(new(new(arguments), AbiShape.Integer(), evidence));
            var returned = Aapcs64.Classify(new(Sequence<AbiShape>.Of(AbiShape.Integer()), shape, evidence));
            if (sample.Reject != !checksum.IsSupported || sample.Reject != !returned.IsSupported)
                throw new InvalidOperationException($"{sample.Type}: checksum={checksum.Unsupported}; return={returned.Unsupported}");
            reports.Add(new { sample.Type, sample.Prefix, sample.Reject, Shape = shape,
                Checksum = checksum.Layout is { } c ? Layout(c) : null, Returned = returned.Layout is { } r ? Layout(r) : null });
        }
        File.WriteAllText(Path.Combine(directory, "layouts.json"), JsonSerializer.Serialize(reports));
        Console.WriteLine($"PASS: {samples.Length} aggregate ABI signatures classified or explicitly rejected");
    }
}
