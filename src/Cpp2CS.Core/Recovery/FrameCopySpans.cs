using Cpp2CS.Flow;
using Cpp2CS.Memory;

namespace Cpp2CS.Recovery;

internal static class FrameCopySpans
{
    internal static IEnumerable<(long Offset, int Size)> Read(MachineFunction function) => CopySpans.Read(function);
}
