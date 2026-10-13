using System.Collections.Immutable;
using System.Runtime.InteropServices;
using Cpp2CS.Nir;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Validation;

public static class NirInputChecks
{
    public static int Run()
    {
        var checks = 0;
        var value = NirValue.Bits(0, 32);
        var effect = NirValue.Effect(1);
        var address = new NirValue(new(2), new NirAddressType("memory", 64));
        var flow = new NirEffectFlow(effect, NirValue.Effect(3));
        var signature = new NirSignature([value.Type], [value.Type]);
        var block = new NirBlock(new(0), [value, effect], [], new NirReturn([value], effect));
        var function = new NirFunction("identity", signature, new(0), [block]);
        var module = new NirModule([function], [], [new("memory", 64, 4096, 4096)], []);
        void Check(bool valid, string reason) { CoreChecks.Require(valid, reason); checks++; }
        void Invalid(NirModule candidate)
        {
            var result = NirValidator.Validate(candidate);
            Check(!result.IsValid && result.Diagnostics.Any(item => item.Code.StartsWith("structure-", StringComparison.Ordinal) ||
                item.Code is "array" or "signature" or "data-bytes" or "function-array" or "block-array" or "operation-array" or "terminator-array"),
                "invalid model structure must return diagnostics before SSA inspection");
        }
        void Function(NirFunction candidate) => Invalid(module with { Functions = [candidate] });
        void Block(NirBlock candidate) => Function(function with { Blocks = [candidate] });
        void Operation(NirOperation operation) => Block(block with { Operations = [operation] });
        void Terminator(NirTerminator terminator) => Block(block with { Terminator = terminator });
        Check(NirValidator.Validate(module).IsValid, "valid public NIR model remains accepted");
        Check(NirValidator.Validate(NirJson.Deserialize(NirJson.Serialize(module))).IsValid, "required JSON fields preserve valid round trips");
        Invalid(null!);
        Invalid(module with { Functions = default });
        Invalid(module with { Externals = default });
        Invalid(module with { MemorySpaces = default });
        Invalid(module with { DataObjects = default });
        Invalid(module with { Functions = [null!] });
        Invalid(module with { Externals = [null!] });
        Invalid(module with { MemorySpaces = [null!] });
        Invalid(module with { DataObjects = [null!] });
        Invalid(module with { Version = null! });
        Invalid(module with { Externals = [new("external", null!, NirExternalEffects.None, NirOutcomes.Return)] });
        Invalid(module with { MemorySpaces = [new(null!, 64, 0, 0)] });
        Invalid(module with { DataObjects = [new("data", null!, 0, [], false)] });
        Invalid(module with { DataObjects = [new("data", "memory", 0, default, false)] });
        Function(function with { Id = null! });
        Function(function with { Signature = null! });
        Function(function with { Signature = new(default, []) });
        Function(function with { Signature = new([], default) });
        Function(function with { Signature = new([null!], []) });
        Function(function with { Signature = new([new NirAddressType(null!, 64)], []) });
        Function(function with { Signature = new([new NirFunctionType(null!)], []) });
        Function(function with { Signature = new([new UnknownType()], []) });
        Function(function with { Blocks = default });
        Function(function with { Blocks = [null!] });
        Function(function with { AdditionalEntries = default });
        Block(block with { Parameters = default });
        Block(block with { Parameters = [default] });
        Block(block with { Operations = default });
        Operation(null!);
        Operation(new UnknownOperation());
        Operation(new NirConstant(default, 0));
        Operation(new NirPure(value, NirPureCode.Add, default));
        Operation(new NirPure(value, NirPureCode.Add, [default]));
        Operation(new NirFunctionConstant(value, null!));
        Operation(new NirLoad(value, address, NirByteOrder.Little, null!));
        Operation(new NirStore(address, value, NirByteOrder.Little, null!));
        Operation(new NirLocalAlloc(address, value, 8, null!));
        Operation(new NirChoose(value, null!));
        Operation(new NirCall(null!, [], [], flow));
        Operation(new NirCall(new NirDirectTarget(null!), [], [], flow));
        Operation(new NirCall(new NirIndirectTarget(default), [], [], flow));
        Operation(new NirCall(new UnknownTarget(), [], [], flow));
        Operation(new NirCall(new NirDirectTarget("identity"), default, [], flow));
        Operation(new NirCall(new NirDirectTarget("identity"), [], default, flow));
        Operation(new NirCall(new NirDirectTarget("identity"), [], [], null!));
        Operation(new NirChoose(value, new(default, effect)));
        Operation(new NirFence(NirMemoryOrder.Acquire, null!));
        Operation(new NirAtomicRmw(value, address, value, NirAtomicCode.Add, NirByteOrder.Little, NirMemoryOrder.Relaxed, null!));
        Operation(new NirCompareExchange(value, NirValue.Bits(4, 1), address, value, value, NirByteOrder.Little,
            NirMemoryOrder.Relaxed, NirMemoryOrder.Relaxed, null!));
        Operation(new NirEnvironmentRead(value, NirEnvironmentField.RoundingMode, null!));
        Operation(new NirEnvironmentWrite(NirEnvironmentField.RoundingMode, value, null!));
        var spec = new BinaryFloatSpec(BinaryFloatKind.Add, 32, 32, BinaryFloatRounding.TiesEven, new());
        var floating = new NirFloat(value, NirValue.Bits(4, 6), spec, [value, value]);
        Operation(floating with { Spec = null! });
        Operation(floating with { Spec = spec with { Rules = null! } });
        Operation(floating with { Inputs = default });
        Operation(floating with { Controls = new(default, value, value, value) });
        Terminator(null!);
        Terminator(new UnknownTerminator());
        Terminator(new NirJump(null!));
        Terminator(new NirJump(new(new(0), default)));
        Terminator(new NirBranch(value, null!, new(new(0), [])));
        Terminator(new NirBranch(value, new(new(0), []), null!));
        Terminator(new NirReturn(default, effect));
        Terminator(new NirReturn([], default));
        Terminator(new NirTailCall(null!, [], effect));
        Terminator(new NirTailCall(new NirDirectTarget("identity"), default, effect));
        Terminator(new NirNoReturnCall(null!, [], effect));
        Terminator(new NirNoReturnCall(new NirDirectTarget("identity"), default, effect));
        Terminator(new NirFault(null!, effect));
        Terminator(new NirTerminate(null!, effect));
        NirType nested = value.Type;
        for (var depth = 0; depth < 66; depth++) nested = new NirFunctionType(new([nested], []));
        Function(function with { Signature = new([nested], []) });
        var cycleTypes = new NirType[1];
        var cycle = new NirSignature(ImmutableCollectionsMarshal.AsImmutableArray(cycleTypes), []);
        cycleTypes[0] = new NirFunctionType(cycle);
        Function(function with { Signature = cycle });
        return checks;
    }

    private sealed record UnknownType : NirType;
    private sealed record UnknownOperation : NirOperation;
    private sealed record UnknownTarget : NirCallTarget;
    private sealed record UnknownTerminator : NirTerminator;
}
