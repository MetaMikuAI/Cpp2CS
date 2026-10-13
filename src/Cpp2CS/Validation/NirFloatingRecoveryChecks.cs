using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Validation;

public static class NirFloatingRecoveryChecks
{
    private const ulong Entry = NirRecoveryChecks.Entry;

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        var operands = new (ulong Left, ulong Right)[]
        {
            (0, 0), (0x8000000000000000, 0), (0x3FF0000000000000, 0x4000000000000000),
            (0x3FF0000000000000, 0x3CA0000000000000), (0x0010000000000000, 0x3FE0000000000000),
            (1, 0x3FF0000000000000), (0x7FEFFFFFFFFFFFFF, 0x4000000000000000),
            (0x7FF0000000000000, 0xFFF0000000000000), (0x7FF8000000000042, 0x7FF0000000000024),
            (0xBFF0000000000000, 0x4000000000000000), (0x4000000000000000, 0x3FF0000000000000)
        };
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var arm = architecture == Architecture.Arm64;
            var operations = new[]
            {
                ("add", arm ? "0028611E" : "F20F58C1"),
                ("mul", arm ? "0008611E" : "F20F59C1"),
                ("div", arm ? "0018611E" : "F20F5EC1"),
                ("minimum", arm ? "0058611E" : "F20F5DC1"),
                ("maximum", arm ? "0048611E" : "F20F5FC1")
            };
            foreach (var (name, encoding) in operations)
            {
                var source = Source(architecture, encoding, arm ? "C0035FD6" : "C3");
                var contract = Contract(architecture, name);
                var result = Recover(source, contract);
                Check(result.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).OfType<NirEnvironmentWrite>().Count() == 1,
                    "one machine floating instruction commits one cumulative exception update");
                foreach (var control in Controls(architecture))
                    foreach (var (left, right) in operands)
                        checks += Compare(source, contract, result.Module, [left, right], control, 0x15);
                var floatingInstruction = source.Instructions.First();
                var statusWrite = floatingInstruction.Operations.Single(operation => operation.Code == OpCode.WriteSlot && operation.Slot == (arm ? "fpsr" : "mxcsr"));
                var combination = floatingInstruction.Operations.Single(operation => operation.Result == statusWrite.Inputs[0]);
                var forged = floatingInstruction with { Operations = floatingInstruction.Operations.Replace(combination, combination with { Code = OpCode.Xor }) };
                Check(RecoveryFloating.Validate(forged) is not null, "status XOR must not pass the proof of sticky OR semantics");
            }
            var compareSource = Source(architecture, arm ? "0020611E" : "660F2EC1",
                arm ? "E0179F1A" : "0F94C0", arm ? "C0035FD6" : "0FB6C0");
            if (!arm) compareSource.Add(compareSource.Instructions.Max(instruction => instruction.Origin.Address + (ulong)instruction.Origin.Bytes.Length), "C3");
            var compareContract = Contract(architecture, "comparison", false);
            var comparison = Recover(compareSource, compareContract);
            foreach (var (left, right) in operands)
                checks += Compare(compareSource, compareContract, comparison.Module, [left, right], arm ? 0U : 0x1F80U, 0);

            var dead = Source(architecture, arm ? "0228611E" : "F20F58C1", arm ? "E00080D2" : "B807000000", arm ? "C0035FD6" : "C3");
            var deadContract = Contract(architecture, "dead_result", false);
            var deadResult = Recover(dead, deadContract);
            Check(deadResult.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).Any(operation => operation is NirFloat),
                "dead numeric result retains its floating exception computation");
            checks += Compare(dead, deadContract, deadResult.Module, [0x7FF0000000000000, 0xFFF0000000000000], arm ? 0U : 0x1F80U, 0);
            var missing = NirInterpreter.Execute(deadResult.Module, deadContract.Name,
                [NirRuntimeValue.Integer(64, 0), NirRuntimeValue.Integer(64, 0)]);
            Check(missing.Status == NirExecutionStatus.MissingInput, "floating environment has no fabricated default");
            var unconditioned = NirRecovery.Recover(dead, [deadContract with { Domain = deadContract.Domain! with { NormalExecution = false } }]);
            Check(!unconditioned.Complete && unconditioned.Gaps.Any(gap => gap.Code == "floating.trap-domain"),
                "machine floating traps cannot be removed without the recorded normal-execution condition");

            var explicitEnvironment = Source(architecture, arm ? "00443BD5" : "0FAE19", arm ? "C0035FD6" : "C3");
            var explicitResult = NirRecovery.Recover(explicitEnvironment, [Contract(architecture, "explicit_machine_environment")]);
            Check(!explicitResult.Complete && explicitResult.Gaps.Any(gap => gap.Code == "contract.floating-environment"),
                "explicit FPCR/MXCSR access remains outside neutral floating projection");
        }
        checks += MathematicalControls();
        checks += LoadFaultOrdering();
        checks += InterfaceAndOperandChecks();
        return checks;
    }

    private static int InterfaceAndOperandChecks()
    {
        var checks = 0;
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var arm = architecture == Architecture.Arm64;
            var control = arm ? 0U : 0x1F80U;
            var single = Source(architecture, arm ? "0028211E" : "F30F58C1", arm ? "C0035FD6" : "C3");
            var singleContract = Contract(architecture, "single_add", width: 32);
            var singleResult = Recover(single, singleContract);
            checks += Compare(single, singleContract, singleResult.Module, [0x3F800000, 0x3F000000], control, 0);
            checks += Compare(single, singleContract, singleResult.Module, [0x3F800000, 0x33800000], control, 0);

            var toInteger = Source(architecture, arm ? "0000789E" : "F2480F2CC0", arm ? "C0035FD6" : "C3");
            var toContract = Contract(architecture, "to_integer", false) with
            { Signature = new([new(64, RecoveryScalarKind.Float)], new(64)) };
            var toResult = Recover(toInteger, toContract);
            foreach (var value in new BigInteger[] { 0x3FF8000000000000, 0xBFF8000000000000, 0x7FF8000000000042 })
                checks += Compare(toInteger, toContract, toResult.Module, [value], control, 0);

            var fromInteger = Source(architecture, arm ? "0000629E" : "F2480F2AC1", arm ? "C0035FD6" : "C3");
            var fromContract = Contract(architecture, "from_integer") with
            { Signature = new([new(64)], new(64, RecoveryScalarKind.Float)) };
            var fromResult = Recover(fromInteger, fromContract);
            foreach (var value in new BigInteger[] { 3, ulong.MaxValue, long.MaxValue })
                checks += Compare(fromInteger, fromContract, fromResult.Module, [value], control, 0);
        }
        foreach (var encoding in new[] { "C4E2F199C2", "C4E2F1A9C2", "C4E2F1B9C2" })
        {
            var source = Source(Architecture.X64, encoding, "C3");
            var contract = Contract(Architecture.X64, "fused_operands") with
            { Signature = new([new(64, RecoveryScalarKind.Float), new(64, RecoveryScalarKind.Float), new(64, RecoveryScalarKind.Float)], new(64, RecoveryScalarKind.Float)) };
            var recovered = Recover(source, contract);
            checks += Compare(source, contract, recovered.Module, [0x4000000000000000, 0x4008000000000000, 0x4014000000000000], 0x1F80, 0);
        }
        return checks;
    }

    private static int MathematicalControls()
    {
        var checks = 0;
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        foreach (var control in Controls(architecture).Concat(architecture == Architecture.Arm64 ? [0x01000800U] : [0x9780U]))
        foreach (var kind in new[] { FloatKind.Add, FloatKind.Mul, FloatKind.Div, FloatKind.Compare })
        foreach (var pair in new (ulong Left, ulong Right)[]
        {
            (0x0010000000000000, 0x3FE0000000000000),
            (0x7FF8000000000042, 0x7FF0000000000024), (1, 0x3FF0000000000000)
        })
        {
            var source = new FloatOperation(kind, 64, kind == FloatKind.Compare ? 4 : 64);
            var expected = FloatEvaluator.Evaluate(architecture, source, pair.Left, pair.Right, control);
            var spec = RecoveryFloating.Specification(architecture, source);
            var fields = Environment(architecture, control, 0);
            var enabled = (fields[NirEnvironmentField.FloatingTrapMask] & 8) != 0;
            spec = spec with { Rounding = (BinaryFloatRounding)(int)fields[NirEnvironmentField.RoundingMode], Rules = spec.Rules with
            {
                SubnormalInput = fields[NirEnvironmentField.FlushSubnormalInput] != 0 ? BinarySubnormalInput.SignedZero : BinarySubnormalInput.Preserve,
                SubnormalOutput = fields[NirEnvironmentField.FlushSubnormalOutput] != 0 && (architecture == Architecture.Arm64 || !enabled)
                    ? spec.Rules.SubnormalOutput : BinarySubnormalOutput.Preserve,
                ExactTinyUnderflow = enabled,
                NaN = fields[NirEnvironmentField.CanonicalNaN] != 0 ? BinaryNaNRule.Canonical : spec.Rules.NaN
            }};
            var actual = BinaryFloatMath.Evaluate(spec, [pair.Left, pair.Right]);
            var bits = kind == FloatKind.Compare ? actual.Bits == 0 ? 6 : actual.Bits == 1 ? 8 : actual.Bits == 2 ? 2 : 3 : actual.Bits;
            CoreChecks.Require(bits == expected.Bits && (uint)actual.Exceptions == expected.Flags,
                $"floating projected controls agree for {architecture}/{kind}/0x{control:X}");
            checks++;
        }
        return checks;
    }

    private static int LoadFaultOrdering()
    {
        var source = Source(Architecture.X64, "F20F5809", "F20F10C1", "C3");
        var contract = Contract(Architecture.X64, "float_memory") with
        { Signature = new([new(64, RecoveryScalarKind.Address), new(64, RecoveryScalarKind.Float)], new(64, RecoveryScalarKind.Float)) };
        var result = Recover(source, contract);
        var context = new NirExecutionContext(result.Module);
        foreach (var pair in Environment(Architecture.X64, 0x1F80, 0x12)) context.Environment.Add(pair.Key, pair.Value);
        var execution = NirInterpreter.Execute(result.Module, contract.Name,
            [NirRuntimeValue.Address("memory", 64, 0x500000), NirRuntimeValue.Integer(64, 0x3FF0000000000000)], context);
        CoreChecks.Require(execution.Status == NirExecutionStatus.Faulted && context.Environment[NirEnvironmentField.FloatingExceptions] == 0x12 &&
            execution.Events.All(item => item.Kind != "EnvironmentWrite"), "faulting machine operand load precedes all sticky floating status commits");
        return 1;
    }

    private static IEnumerable<uint> Controls(Architecture architecture)
    {
        for (var rounding = 0; rounding < 4; rounding++)
        for (var settings = 0; settings < 4; settings++)
            yield return architecture == Architecture.Arm64
                ? (uint)(rounding << 22 | (settings & 1) << 24 | (settings >> 1) << 25)
                : (uint)(0x1F80 | rounding << 13 | (settings & 1) << 6 | (settings >> 1) << 15);
    }

    private static Dictionary<NirEnvironmentField, BigInteger> Environment(Architecture architecture, uint control, uint status)
    {
        var arm = architecture == Architecture.Arm64;
        var rawRound = (control >> (arm ? 22 : 13)) & 3;
        var rounding = rawRound switch
        {
            0 => BinaryFloatRounding.TiesEven, 1 => arm ? BinaryFloatRounding.PlusInfinity : BinaryFloatRounding.MinusInfinity,
            2 => arm ? BinaryFloatRounding.MinusInfinity : BinaryFloatRounding.PlusInfinity, _ => BinaryFloatRounding.TowardZero
        };
        var traps = arm ? (control >> 8 & 31) | (control >> 10 & 32) : CanonicalFlags(~control >> 7);
        return new()
        {
            [NirEnvironmentField.RoundingMode] = (int)rounding,
            [NirEnvironmentField.FlushSubnormalInput] = control >> (arm ? 24 : 6) & 1,
            [NirEnvironmentField.FlushSubnormalOutput] = control >> (arm ? 24 : 15) & 1,
            [NirEnvironmentField.CanonicalNaN] = arm ? control >> 25 & 1 : 0,
            [NirEnvironmentField.FloatingTrapMask] = traps,
            [NirEnvironmentField.FloatingExceptions] = status
        };
    }

    private static uint CanonicalFlags(uint mxcsr) => (mxcsr & 1) | (mxcsr >> 1 & 30) | (mxcsr << 4 & 32);
    private static uint MachineFlags(uint canonical, bool arm) => arm ? (canonical & 31) | (canonical << 2 & 128)
        : (canonical & 1) | (canonical << 1 & 60) | (canonical >> 4 & 2);

    private static int Compare(NirRecoveryChecks.FixtureSource source, FunctionContract contract, NirModule module,
        BigInteger[] arguments, uint control, uint status)
    {
        var state = NirRecoveryChecks.InitialState(source.Architecture, [], source.Addresses);
        var abi = MachineAbi.Describe(contract);
        for (var index = 0; index < arguments.Length; index++)
        {
            var location = (SlotArgumentLocation)abi.Arguments[index];
            state.Slots[location.Slot] = arguments[index];
        }
        var arm = source.Architecture == Architecture.Arm64;
        state.Slots[arm ? "fpcr" : "mxcsr"] = arm ? control : control | MachineFlags(status, false);
        if (arm) state.Slots["fpsr"] = MachineFlags(status, true) | (1U << 27);
        NirRecoveryChecks.ExecuteMachine(source, Entry, state);
        var context = new NirExecutionContext(module);
        foreach (var pair in Environment(source.Architecture, control, status)) context.Environment.Add(pair.Key, pair.Value);
        var nir = NirInterpreter.Execute(module, contract.Name, arguments.Select((argument, index) =>
            NirRuntimeValue.Integer(contract.Signature.Arguments[index].Width, argument)).ToImmutableArray(), context);
        var expected = state.Slots[((SlotArgumentLocation)abi.Result!).Slot] & ((BigInteger.One << abi.Result.Width) - 1);
        var statusBits = (uint)state.Slots[arm ? "fpsr" : "mxcsr"];
        var expectedStatus = arm ? (statusBits & 31) | (statusBits >> 2 & 32) : CanonicalFlags(statusBits);
        CoreChecks.Require(nir.Status == NirExecutionStatus.Returned && nir.Values.Single().Bits == expected,
            $"floating MIR+RET/NIR numeric result {source.Architecture}/{contract.Name}/0x{control:X}: {nir.Status}: {nir.Detail}");
        CoreChecks.Require(context.Environment[NirEnvironmentField.FloatingExceptions] == expectedStatus,
            "floating MIR/NIR sticky exceptions agree with preexisting status preserved");
        return 2;
    }

    private static NirRecoveryChecks.FixtureSource Source(Architecture architecture, params string[] encodings)
    {
        var source = new NirRecoveryChecks.FixtureSource(architecture, "fixture:nir-floating-recovery");
        source.Add(Entry, encodings);
        return source;
    }
    private static FunctionContract Contract(Architecture architecture, string name, bool floatingResult = true, int width = 64) => new(name, Entry,
        new([new(width, RecoveryScalarKind.Float), new(width, RecoveryScalarKind.Float)], new(floatingResult ? width : 64,
            floatingResult ? RecoveryScalarKind.Float : RecoveryScalarKind.Integer)),
        architecture == Architecture.Arm64 ? MachineAbiKind.Aapcs64 : MachineAbiKind.WindowsX64,
        new(true, true, true, false, true, false, false), ["handwritten native scalar floating interface"], new(true, true, true, true));
    private static NirRecoveryResult Recover(NirRecoveryChecks.FixtureSource source, FunctionContract contract)
    {
        var result = NirRecovery.Recover(source, [contract]);
        CoreChecks.Require(result.Complete, NirRecoveryChecks.Explain(result));
        var text = NirJson.Serialize(result.Module);
        var detached = NirJson.Deserialize(text);
        CoreChecks.Require(NirValidator.Validate(detached).IsValid && NirJson.Serialize(detached) == text &&
            !text.Contains("mxcsr", StringComparison.OrdinalIgnoreCase) && !text.Contains("fpcr", StringComparison.OrdinalIgnoreCase),
            "floating NIR round trip is valid and contains no packed machine control register");
        return result with { Module = detached };
    }
}
