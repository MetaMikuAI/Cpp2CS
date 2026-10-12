using System.Globalization;
using System.Numerics;
using System.Text.Json;
using Cpp2CS;
using Cpp2CS.Ir;
using Cpp2CS.Validation;

if (args is ["selftest"]) { Console.WriteLine(FloatChecks.Run()); return; }
while (Console.ReadLine() is { } line)
{
    using var document = JsonDocument.Parse(line);
    var r = document.RootElement;
    var spec = new FloatOperation(Enum.Parse<FloatKind>(r.GetProperty("kind").GetString()!),
        r.GetProperty("width").GetInt32(), r.GetProperty("resultWidth").GetInt32(),
        Enum.Parse<FloatRounding>(r.GetProperty("rounding").GetString()!));
    var output = FloatEvaluator.Evaluate(Enum.Parse<Architecture>(r.GetProperty("arch").GetString()!),
        spec, BigInteger.Parse("0" + r.GetProperty("a").GetString(), NumberStyles.HexNumber),
        BigInteger.Parse("0" + r.GetProperty("b").GetString(), NumberStyles.HexNumber),
        r.GetProperty("control").GetUInt32());
    Console.WriteLine(JsonSerializer.Serialize(new { bits = output.Bits.ToString("x"), output.Flags, output.TrapFlags }));
}
