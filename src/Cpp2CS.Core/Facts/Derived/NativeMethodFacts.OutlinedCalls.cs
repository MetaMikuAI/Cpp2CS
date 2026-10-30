using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Facts.Derived;

internal sealed partial class NativeMethodFacts
{
    internal readonly Dictionary<(ulong, Read?), (MachineFunction Function, IdiomResult Idioms)?> outlinedCalls = new();

    internal (MachineFunction Function, IdiomResult Idioms)? OutlinedCall(ulong address, Read? returned = null)
    {
        if (outlinedCalls.TryGetValue((address, returned), out var cached)) return cached;
        (MachineFunction, IdiomResult)? result = null;
        if (facts.Helpers.At(address)?.Kind == HelperKind.Unknown && facts.Code.At(address) is { } range
            && range.Start == address && range.Size <= 1024 && range.ExceptionRegions.Length == 0
            && lifter.Lift(address, returned) is { Succeeded: true } lifted)
        {
            var idioms = rewriter.Run(lifted.Function);
            if (idioms.Errors.Count == 0 && idioms.Residuals.All(r => r.Category.StartsWith("slot-read-without-init:")))
                result = (lifted.Function, idioms);
        }
        return outlinedCalls[(address, returned)] = result;
    }
}
