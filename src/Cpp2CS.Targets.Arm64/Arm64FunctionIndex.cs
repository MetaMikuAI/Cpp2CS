using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;

namespace Cpp2CS.Targets.Arm64;

/// <summary>直接调用目标的集合只作发现索引；忽略调用顺序、重复次数与帧指令。</summary>
public static class Arm64FunctionIndex
{
    public static ImmutableHashSet<CallTarget>? Create(IImage image, FunctionRange range)
    {
        if (!range.HasConsistentExtent || range.Length % 4 != 0 || !image.IsExecutable(range.Start, range.Length)) return null;
        var calls = ImmutableHashSet.CreateBuilder<CallTarget>();
        for (ulong offset = 0; offset < range.Length; offset += 4)
        {
            ulong address = range.Start + offset;
            uint word = (uint)image.ReadUnsigned(address, 4);
            if ((word & 0x7c000000) != 0x14000000) continue;
            long displacement = ((long)(word & 0x03ffffff) << 38) >> 36;
            ulong target = unchecked(address + (ulong)displacement);
            if (((word & 0x80000000) != 0 || target < range.Start || target - range.Start >= range.Length)
                && Arm64DirectCalls.ResolveTarget(image, new ImageFunction(target)).Target is { } resolved) calls.Add(resolved);
        }
        return calls.ToImmutable();
    }
}
