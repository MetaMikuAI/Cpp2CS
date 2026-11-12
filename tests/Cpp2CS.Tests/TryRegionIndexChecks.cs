using Cpp2CS.Native.Images;
namespace Cpp2CS.Tests;
internal static class TryRegionIndexChecks
{
    public const string Command = "try-region-index";
    public static int Run()
    {
        var checks = new Assertions();
        TryRegion[] regions = [new(10, 30, 1, []), new(10, 2, 2, []), new(20, 5, 3, []),
            new(50, 2, null, []), new(60, 0, 4, []), new(ulong.MaxValue - 2, 8, 5, [])];
        bool Linear(ulong address) => regions.Any(r => r.Handler is not null && address >= r.Start && address - r.Start < r.Length);
        var index = new TryRegionIndex(regions);
        checks.True(Enumerable.Range(0, 100).Select(i => (ulong)i).Append(ulong.MaxValue)
            .All(p => index.HasHandlerAt(p) == Linear(p)), "重叠、同起点、空区间、无处理入口与地址末尾保持原判定");
        var random = new Random(7171);
        regions = Enumerable.Range(0, 2000).Select(_ => new TryRegion((ulong)random.Next(10000), (ulong)random.Next(100),
            random.Next(3) == 0 ? null : 1UL, [])).ToArray();
        index = new TryRegionIndex(regions.Reverse());
        checks.True(Enumerable.Range(0, 10200).All(p => index.HasHandlerAt((ulong)p) == Linear((ulong)p)), "无序输入的索引与逐项查询一致");
        checks.True(Enumerable.Range(0, 10200).All(p => index.HasHandlerInRange((ulong)p, 17) == regions.Any(r =>
            r.Handler is not null && r.Length != 0 && (ulong)p < r.Start + r.Length && r.Start < (ulong)p + 17)), "区间相交查询与逐项判定一致");
        checks.True(Enumerable.Range(0, 10200).All(p => index.InRange((ulong)p, 17).OrderBy(r => r.Start).SequenceEqual(
            regions.Reverse().Where(r => r.Handler is not null && r.Length != 0 && (ulong)p < r.Start + r.Length && r.Start < (ulong)p + 17).OrderBy(r => r.Start))),
            "相交区域枚举与逐项判定一致且保持同起点次序");
        checks.True(!index.HasHandlerInRange(10, 0), "空查询区间不相交");
        checks.True(!new TryRegionIndex([]).HasHandlerAt(0), "空表不包含处理入口");
        return checks.Finish("异常区域索引");
    }
}
