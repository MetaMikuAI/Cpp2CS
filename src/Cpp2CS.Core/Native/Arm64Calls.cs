using Cpp2CS.Abi;

namespace Cpp2CS.Native;

public static class Arm64Calls
{
    // NoReturn 仅描述控制流，不决定参数个数。
    public static int? HelperArgumentCount(string? helper) => helper switch
    {
        "ResolveInterface" or "CxxThrow" => 3,
        "IsAssignable" or "Box" or "IsInstance" or "AllocateArray" => 2,
        "InitializeMetadata" or "InitializeClass" or "EnsureClassMetadata" or "ResolveMetadata" or "Allocate" or
        "WriteBarrier" or "CxxBeginCatch" or "CxxAllocateException" or "UnwindResume" or "RethrowException" or
        "RaiseException" or "ThrowInvalidCast" or "CxxCatchTerminate" => 1,
        "ThrowNullReference" or "ThrowIndexOutOfRange" or "CreateArrayTypeMismatchException" or "CxxEndCatch" => 0,
        _ => null
    };
    public static bool PreservesCallerStack(string? helper) => helper is
        "WriteBarrier" or "InitializeMetadata" or "InitializeClass" or "EnsureClassMetadata" or "ResolveMetadata" or
        "ResolveInterface" or "IsAssignable" or "Allocate" or "CxxBeginCatch" or "CxxEndCatch" or "Box" or
        "AllocateArray" or "IsInstance" or "CreateArrayTypeMismatchException";
    public static IEnumerable<string> Inputs(MachineCall call, Symbols symbols, NativeAbi abi, RuntimeProfile runtime)
    {
        if (call.Target.Operation != "constant") return Arm64Registers.CallInputs;
        var target = unchecked((ulong)call.Target.Immediate);
        if (runtime.Helpers.TryGetValue(target, out var helper) && HelperArgumentCount(helper.Kind) is { } count)
            return Enumerable.Range(0, count).Select(n => $"x{n}");
        var candidates = symbols.Methods.GetValueOrDefault(target, []);
        var layouts = candidates.Select(m => abi.Classify(abi.Normalize(m))).ToArray();
        if (layouts.Length == 0 || layouts.Any(l => l is null)) return Arm64Registers.CallInputs;
        return layouts.SelectMany(l => l!.Arguments.SelectMany(a => a.Pieces)
            .Concat(l.Return.Indirect ? l.Return.Pieces : [])).Select(p => p.Location is RegisterLocation r ? Arm64Registers.Canonical(r.Name) : "sp").Distinct();
    }
}
