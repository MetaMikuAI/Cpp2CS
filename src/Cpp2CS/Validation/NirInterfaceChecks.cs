using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Validation;

public static class NirInterfaceChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(bool passed, string reason) { CoreChecks.Require(passed, reason); checks++; }
        foreach (var abi in new[] { MachineAbiKind.Aapcs64, MachineAbiKind.WindowsX64 })
        {
            var arm = abi == MachineAbiKind.Aapcs64;
            var floating = new RecoveryScalarType(64, RecoveryScalarKind.Float);
            var contract = new FunctionContract("identity", 0x1000, new([floating], floating), abi,
                new(false, false, false, false, true, false, false), ["non-variadic scalar interface"], new(true, true, true, true));
            var mapping = MachineAbi.Describe(contract);
            Check(mapping.Arguments[0] == new SlotArgumentLocation(arm ? "v0" : "xmm0", 0, 64), "floating input follows the scalar ABI");
            Check(mapping.Result == new SlotArgumentLocation(arm ? "v0" : "xmm0", 0, 64), "floating result follows the scalar ABI");
            var mixed = contract with { Signature = new([new(64), floating, new(32), floating, floating], floating) };
            var locations = MachineAbi.Describe(mixed).Arguments;
            Check(locations[0] == new SlotArgumentLocation(arm ? "x0" : "rcx", 0, 64), "integer input uses general registers");
            Check(locations[1] == new SlotArgumentLocation(arm ? "v0" : "xmm1", 0, 64), "AAPCS register classes advance independently; Windows uses argument position");
            Check(locations[2] == new SlotArgumentLocation(arm ? "x1" : "r8", 0, 32), "mixed argument sequence retains integer width");
            Check(locations[4] == (arm ? (MachineArgumentLocation)new SlotArgumentLocation("v2", 0, 64) : new StackArgumentLocation(40, 64)), "Windows fifth argument occupies its stack slot");
            var many = contract with { Signature = new(Enumerable.Repeat(floating, 10).Append(new RecoveryScalarType(64)).ToImmutableArray(), floating) };
            var spilled = MachineAbi.Describe(many).Arguments;
            Check(spilled[8] == new StackArgumentLocation(arm ? 0 : 72, 64), "floating register exhaustion creates stack arguments");
            Check(spilled[10] == (arm ? (MachineArgumentLocation)new SlotArgumentLocation("x0", 0, 64) : new StackArgumentLocation(88, 64)), "AAPCS general arguments remain available after floating spill");
            Check(!MachineAbi.TryDescribe(contract with { Signature = new([new(16, RecoveryScalarKind.Float)], floating) }, out _, out _), "unsupported floating ABI widths remain explicit");
            var summary = MachineAbi.CreateSummary(contract);
            Check(DerivedGraphValidator.ValidateSummary(summary).Count == 0, "floating summary preserves all unrelated ABI state");
            var relation = summary.NormalOutputs.Single(item => item.Slot == ((SlotArgumentLocation)mapping.Result!).Slot);
            Check(relation.Segments is [{ Width: 64, Kind: SlotRelationKind.Result }, { Width: 64, Kind: SlotRelationKind.Havoc }], "upper floating result bits remain unspecified");
            var index = new FunctionContractIndex([contract]);
            Check(ReferenceEquals(index.Summary(contract), index.Summary(contract)), "shared index reuses a single authoritative summary");
            var instruction = RecoveryGraphChecks.Decode(MachineAbi.ArchitectureFor(abi), 0x1000, arm ? "C0035FD6" : "C3");
            var source = new Source(instruction);
            var recovered = NirRecovery.RecoverOne(source, contract, index);
            Check(recovered.Complete && recovered.Module.Functions.Length == 1, "floating identity is recovered through the indexed function API");
            var detached = NirJson.Deserialize(NirJson.Serialize(recovered.Module));
            foreach (var bits in new BigInteger[] { 0, BigInteger.One << 63, 0x3FF0000000000000, 0x7FF8000000000017 })
            {
                var execution = NirInterpreter.Execute(detached, contract.Name, [NirRuntimeValue.Integer(64, bits)]);
                Check(execution.Status == NirExecutionStatus.Returned && execution.Values[0].Bits == bits,
                    "logical floating interface preserves zero signs, normal encodings and NaN payloads");
            }
        }
        return checks;
    }

    private sealed class Source(MirInstruction instruction) : IRegionInstructionSource
    {
        public string ImageId => instruction.Origin.ImageId;
        public Architecture Architecture => instruction.Architecture;
        public InstructionDecodeResult Decode(ulong address) => address == instruction.Origin.Address
            ? InstructionDecodeResult.Supported(instruction) : InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unmapped, "fixture address unavailable");
    }
}
