using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json;
using Sekai.Mysekai;

if (Unsafe.SizeOf<GridPosition>() != 4) throw new Exception("native value layout");
var setter = typeof(GridAreaCell).GetProperty("TilePosition")!.GetSetMethod(true)!;
if (!setter.IsPrivate) throw new Exception("setter visibility");
var assign = setter.CreateDelegate<Action<GridAreaCell,GridPosition>>();
var oracle = JsonDocument.Parse(File.ReadAllText(args[0])).RootElement;
int checks = 2;
foreach (var row in oracle.GetProperty("rows").EnumerateArray())
{
    var value = new GridAreaCell();
    if (Unsafe.BitCast<GridPosition,uint>(value.TilePosition) != 0) throw new Exception("new object initialization");
    assign(value,Unsafe.BitCast<uint,GridPosition>(row.GetProperty("input").GetUInt32()));
    if (Unsafe.BitCast<GridPosition,uint>(value.TilePosition) != row.GetProperty("setterResult").GetUInt32()) throw new Exception("private setter bits");
    value.SetPosition(Unsafe.BitCast<uint,GridPosition>(row.GetProperty("other").GetUInt32()));
    if (Unsafe.BitCast<GridPosition,uint>(value.TilePosition) != row.GetProperty("methodResult").GetUInt32()) throw new Exception("method bits");
    checks += 3;
}
File.WriteAllText(Path.Combine(Path.GetDirectoryName(Path.GetFullPath(args[0]))!,"verification.json"),JsonSerializer.Serialize(new
{
    passed=true, assertions=checks, nativeCalls=oracle.GetProperty("nativeCalls").GetInt32(),
    completeTypes=new[] { "Sekai.Mysekai.GridAreaCell" }, methods=4,
    partialDependencies=new[] { "Sekai.Mysekai.GridPosition: layout only" }, gridAreaDataComplete=false, apiChainComplete=false
},new JsonSerializerOptions { WriteIndented=true }));
Console.WriteLine($"PASS: {checks} assertions; GridAreaCell 4 methods; GridPosition layout only");
