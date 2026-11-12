using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Native.Images;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet : IImageInstructionSet, IExceptionFlowProvider, IExceptionModel
{
    public IImage Image => image;
    public ImmutableArray<TryRegion> Regions => image.TryRegions;
    public TryRegionIndex RegionIndex { get; } = new(image.TryRegions);
    public IExceptionModel ExceptionModel => this;
    // LLVM AArch64TargetLowering 的 getExceptionPointerRegister、getExceptionSelectorRegister 给出入口单元。
    public void EnterHandler(IRegisterState state, Term exception, Term selector)
    {
        state.Write(Arm64Registers.X[0], exception);
        state.Write(Arm64Registers.X[1], selector);
    }
    public bool IsResumeUnwind(CallTarget target) =>
        ResolveCallTarget(image, target) is ImportedTarget { Symbol.Name: "_Unwind_Resume" };
    public Term ResumeException(IRegisterReader state) => state.Read(Arm64Registers.X[0]);
}
