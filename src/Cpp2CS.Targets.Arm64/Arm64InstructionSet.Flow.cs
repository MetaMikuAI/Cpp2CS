using Cpp2CS.Native.Images;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet : IImageInstructionSet
{
    public IImage Image => image;
}
