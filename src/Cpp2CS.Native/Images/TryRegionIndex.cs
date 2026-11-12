namespace Cpp2CS.Native.Images;

/// <summary>按起点与前缀最远终点索引有处理入口的区域；重叠区域保持并集语义。</summary>
public sealed class TryRegionIndex
{
    private readonly ulong[] starts;
    private readonly ulong[] last;
    public TryRegionIndex(IEnumerable<TryRegion> regions)
    {
        var ordered = regions.Where(r => r.Handler is not null && r.Length != 0).OrderBy(r => r.Start).ToArray();
        starts = new ulong[ordered.Length];
        last = new ulong[ordered.Length];
        for (int i = 0; i < ordered.Length; i++)
        {
            var region = ordered[i];
            starts[i] = region.Start;
            // 与无符号差值的包含判定一致，允许区间延伸到地址空间末尾。
            ulong end = region.Length - 1 > ulong.MaxValue - region.Start ? ulong.MaxValue : region.Start + region.Length - 1;
            last[i] = i == 0 ? end : Math.Max(last[i - 1], end);
        }
    }
    public bool HasHandlerAt(ulong address) => HasHandlerInRange(address, 1);
    public bool HasHandlerInRange(ulong start, ulong length)
    {
        if (length == 0) return false;
        ulong end = length - 1 > ulong.MaxValue - start ? ulong.MaxValue : start + length - 1;
        int low = 0, high = starts.Length;
        while (low < high)
        {
            int middle = low + (high - low) / 2;
            if (starts[middle] <= end) low = middle + 1; else high = middle;
        }
        return low != 0 && start <= last[low - 1];
    }
}
