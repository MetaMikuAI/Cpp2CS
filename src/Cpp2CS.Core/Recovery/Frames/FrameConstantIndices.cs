using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery;

internal static class FrameConstantIndices
{
    internal static int Run(MachineFunction function) => FrameIndexAnalysis.Run(function);
}
