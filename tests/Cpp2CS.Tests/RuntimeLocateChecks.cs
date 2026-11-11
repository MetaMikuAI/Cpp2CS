using Cpp2CS.Runtime;
using Cpp2CS.Native;
using Cpp2CS.Recovery.RuntimeFunctions;

namespace Cpp2CS.Tests;

internal static class RuntimeLocateChecks
{
    public const string Command = "runtime-locate";
    public static int Run()
    {
        var checks = new Assertions();
        foreach (var path in RuntimeCatalogChecks.Paths())
        {
            var catalog = RuntimeCatalogChecks.Load(path);
            foreach (var function in catalog.Functions)
            {
                var recognition = function.Recognition;
                checks.True(recognition.Import is null || recognition.Import == function.MangledName,
                    function.Name + " 精确导入身份");
                checks.True(recognition.Export is null && recognition.CallGraph is null && recognition.ReferenceShape is null,
                    function.Name + " 未支持的依据不得静默登记");
                checks.True(function.Basis.Length > 0, function.Name + " 来源");
            }
            checks.True(catalog.Functions.Where(f => f.Recognition.Import is not null)
                .GroupBy(f => f.Recognition.Import).All(g => g.Count() == 1), "导入名唯一");
        }
        var selected = RuntimeFunctionCatalog.Select("2022.3.62f2", "aarch64-linux-android", "LP64");
        var same = selected.Functions.Where(f => f.Recognition.Symbol).GroupBy(f => f.Operation).First(g => g.Count() >= 2).Take(2).ToArray();
        var different = selected.Functions.First(f => f.Recognition.Symbol && f.Operation != same[0].Operation);
        var image = new InputMemoryImage { FunctionSymbols = [new(same[0].MangledName, 64, 0), new(same[1].MangledName, 64, 8)] };
        var locations = RuntimeFunctionLocations.Locate(image, selected, t => t is ImageFunction { EntryOffset: 32 } ? new ImageFunction(64) : t);
        checks.True(locations.Find(32)?.Function == locations.Find(64)?.Function && locations.Find(64) is not null, "归一后按符号入口查询");
        checks.True(locations.Entries[64].Candidates.Length == 2 && locations.Entries[64].Reason is not null, "同操作别名保留全部候选与选择原因");
        image = new InputMemoryImage { FunctionSymbols = [new(same[0].MangledName, 64, 8), new(different.MangledName, 64, 8)] };
        locations = RuntimeFunctionLocations.Locate(image, selected, t => t);
        checks.True(locations.Find(64) is null && locations.Entries[64].Candidates.Length == 2 && locations.Entries[64].Reason is not null, "不同操作别名不定位并记录原因");
        checks.True(RuntimeFunctionLocations.Locate(new InputMemoryImage(), selected, t => t).Find(64) is null, "无符号不猜入口");
        return checks.Finish("运行时定位识别数据");
    }
}
