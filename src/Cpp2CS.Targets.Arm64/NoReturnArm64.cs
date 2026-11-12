using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet : INoReturnInstructionSet
{
    public bool IsStraightLineFailure(Reason reason) => reason.Code is
        "arm64.floating" or "arm64.vector" or "arm64.exclusive" or "arm64.atomic" or "arm64.barrier";

    public CallTarget ResolveCallTarget(IImage source, CallTarget target)
        => Arm64DirectCalls.ResolveTarget(source, target).Target ?? target;
}
