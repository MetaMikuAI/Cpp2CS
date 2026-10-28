using Cpp2CS.Flow;
using Cpp2CS.Memory;

namespace Cpp2CS.Recovery;

internal static class FrameConstantIndices
{
    internal static int Run(MachineFunction function) => FrameIndexAnalysis.Run(function);
}
