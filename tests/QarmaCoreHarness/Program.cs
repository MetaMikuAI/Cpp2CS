using Cpp2CS.Ir;
using System.Globalization;
using System.Numerics;

while (Console.ReadLine() is { } line)
{
    var parts = line.Split(' ');
    if (parts.Length != 4) throw new InvalidDataException("Expected data modifier keyHigh keyLow");
    var data = ulong.Parse(parts[0], NumberStyles.HexNumber);
    var modifier = ulong.Parse(parts[1], NumberStyles.HexNumber);
    var key = (new BigInteger(ulong.Parse(parts[2], NumberStyles.HexNumber)) << 64) |
        ulong.Parse(parts[3], NumberStyles.HexNumber);
    Console.WriteLine(Qarma64.Evaluate(data, modifier, key).ToString("X16"));
}
