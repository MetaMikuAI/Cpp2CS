using Cpp2CS.Native.Images;

namespace Cpp2CS.Targets.Arm64;

public static class Arm64DirectCalls
{
    /// <summary>线性扫描范围内的 BL 和向范围外的 B；不依赖可提升性或不返回分析的路径截断。</summary>
    public static IEnumerable<(ulong Address, ulong Target)> ToCandidates(IImage image, FunctionRange range, IReadOnlySet<ulong> candidates)
    {
        for (ulong offset = 0; offset + 4 <= range.Length; offset += 4)
        {
            var address = checked(range.Start + offset);
            if (!image.IsExecutable(address, 4)) continue;
            uint word = (uint)image.ReadUnsigned(address, 4);
            if ((word & 0x7c000000) != 0x14000000) continue;
            long displacement = ((long)(word & 0x03ffffff) << 38) >> 36;
            ulong target = unchecked(address + (ulong)displacement);
            bool linked = (word & 0x80000000) != 0;
            if ((linked || target < range.Start || target - range.Start >= range.Length) && candidates.Contains(target))
                yield return (address, target);
        }
    }
}
