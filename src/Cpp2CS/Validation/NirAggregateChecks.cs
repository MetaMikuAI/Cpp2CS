using System.Collections.Immutable;
using System.Numerics;
using System.Text.Json;
using Cpp2CS.Ir;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Validation;

public static class NirAggregateChecks
{
    private static readonly RecoveryScalarType U64 = new(64);
    private static readonly RecoveryScalarType F64 = new(64, RecoveryScalarKind.Float);
    private static readonly RecoveryScalarType Pair = Aggregate(8, U64, U64);
    private static readonly RecoveryScalarType Hfa = Aggregate(8, F64, F64);

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string detail) { CoreChecks.Require(condition, detail); checks++; }
        var pair = Contract(MachineAbiKind.Aapcs64, "pair", 0x1000, [Pair], Pair);
        var pairMap = MachineAbi.Describe(pair);
        Check(MachineAbi.Pieces(pairMap.Arguments[0]).SequenceEqual(new MachineValuePart[]
            { new(0, new SlotArgumentLocation("x0", 0, 64)), new(64, new SlotArgumentLocation("x1", 0, 64)) }),
            "AAPCS64 ordinary pair occupies two consecutive general registers");
        var aligned = Aggregate(16, U64, U64);
        var alignedContract = pair with { Signature = new([U64, aligned, U64], aligned) };
        Check(!MachineAbi.TryDescribe(alignedContract, out _, out _),
            "whole-aggregate over-alignment is not confused with AAPCS64 member natural alignment");
        var naturalContract = pair with { Signature = new([U64, Pair, U64], Pair) };
        var naturalMap = MachineAbi.Describe(naturalContract);
        Check(MachineAbi.Pieces(naturalMap.Arguments[1]).First().Location == new SlotArgumentLocation("x1", 0, 64) &&
            naturalMap.Arguments[2] == new SlotArgumentLocation("x3", 0, 64), "naturally aligned pair does not skip an available general register");
        var spillArguments = Enumerable.Repeat(U64, 7).Append(Pair).Append(U64).ToImmutableArray();
        var spillContract = pair with { Signature = new(spillArguments, Pair) };
        var spillMap = MachineAbi.Describe(spillContract);
        Check(spillMap.Arguments[7] == new StackArgumentLocation(0, 128) && spillMap.Arguments[8] == new StackArgumentLocation(16, 64),
            "AAPCS64 insufficient general registers spill the complete aggregate and exhaust the general bank");
        var alignedSpill = pair with { Signature = new(Enumerable.Repeat(U64, 9).Append(aligned).ToImmutableArray(), aligned) };
        Check(!MachineAbi.TryDescribe(alignedSpill, out _, out _),
            "unsupported overall alignment does not move a spilled aggregate to a guessed stack offset");
        var overalignedHfa = Aggregate(16, F64, F64);
        var overalignedHfaSpill = pair with { Signature = new(Enumerable.Repeat(F64, 9).Append(overalignedHfa).ToImmutableArray(), F64) };
        Check(!MachineAbi.TryDescribe(overalignedHfaSpill, out _, out _),
            "overaligned HFA stack placement requires the distinct natural alignment which the schema does not represent");
        var naturalHfaSpill = pair with { Signature = new(Enumerable.Repeat(F64, 9).Append(Hfa).ToImmutableArray(), F64) };
        Check(MachineAbi.Describe(naturalHfaSpill).Arguments[9] == new StackArgumentLocation(8, 128),
            "naturally aligned spilled HFA follows the preceding stack double without a guessed sixteen-byte boundary");
        var hfaArguments = Enumerable.Repeat(F64, 7).Append(Hfa).Append(F64).Append(U64).ToImmutableArray();
        var hfaContract = pair with { Signature = new(hfaArguments, Hfa) };
        var hfaMap = MachineAbi.Describe(hfaContract);
        Check(hfaMap.Arguments[7] == new StackArgumentLocation(0, 128) && hfaMap.Arguments[8] == new StackArgumentLocation(16, 64) &&
            hfaMap.Arguments[9] == new SlotArgumentLocation("x0", 0, 64), "HFA spill exhausts only the SIMD bank and reserves its complete size");
        var floatFour = Aggregate(8, Hfa, Hfa);
        var nested = pair with { Signature = new([floatFour], floatFour) };
        Check(MachineAbi.Pieces(MachineAbi.Describe(nested).Result!).Count() == 4,
            "nested homogeneous aggregate flattens to four SIMD result registers even above 16 bytes");
        var narrowPair = Aggregate(4, new(32), new(32), new(32));
        var narrowMap = MachineAbi.Describe(pair with { Signature = new([narrowPair], narrowPair) });
        Check(MachineAbi.Pieces(narrowMap.Result!).Last().Location == new SlotArgumentLocation("x1", 0, 32),
            "unused register bits after a 12-byte aggregate are excluded from the logical value");

        var restored = JsonSerializer.Deserialize<FunctionContract>(JsonSerializer.Serialize(pair))!;
        Check(MachineAbi.TypeEquals(pair.Signature.Result, restored.Signature.Result), "aggregate layout comparison is structural after JSON reload");
        Check(DerivedGraphValidator.ValidateSummary(MachineAbi.CreateSummary(restored)).Count == 0, "rebuilt composite summaries validate by structure");
        var summary = MachineAbi.CreateSummary(pair);
        var badOutputs = summary.NormalOutputs.Select(output => output.Slot == "x1"
            ? output with { Segments = output.Segments.Select(segment => segment.Kind == SlotRelationKind.Result
                ? segment with { ResultOffset = 0 } : segment).ToImmutableArray() } : output).ToImmutableArray();
        Check(DerivedGraphValidator.ValidateSummary(summary with { NormalOutputs = badOutputs }).Count != 0,
            "summary validation rejects a second result register bound to the first logical lane");
        Check(DerivedGraphValidator.ValidateSummary(summary with { Interface = summary.Interface with
            { Result = new CompositeArgumentLocation(128, default) } }).Count != 0, "summary validation rejects absent composite parts");
        Check(DerivedGraphValidator.ValidateSummary(summary with { Interface = summary.Interface with
            { Result = new CompositeArgumentLocation(128, [new(64, new SlotArgumentLocation("x0", 0, 64)), new(0, new SlotArgumentLocation("x1", 0, 64))]) } }).Count != 0,
            "summary validation rejects rearranged result pieces");
        var nullField = Pair with { Aggregate = new(8, [null!]) };
        Check(!MachineAbi.TryDescribe(pair with { Signature = new([nullField], Pair) }, out _, out _) &&
            !MachineAbi.TypeEquals(nullField, nullField), "null external layout fields are rejected without hiding logic exceptions");
        var deep = U64;
        for (var depth = 0; depth < 35; depth++) deep = Aggregate(8, deep);
        Check(!MachineAbi.TryDescribe(pair with { Signature = new([deep], Pair) }, out _, out _) &&
            !MachineAbi.TypeEquals(deep, deep), "aggregate validation and comparison both bound recursive layout depth");

        foreach (var abi in new[] { MachineAbiKind.Aapcs64, MachineAbiKind.WindowsX64 })
        {
            var arm = abi == MachineAbiKind.Aapcs64;
            var type = arm ? Pair : Aggregate(4, new(32), new(32));
            var contract = Contract(abi, "identity", 0x1000, [type], type);
            if (!arm)
                Check(MachineAbi.Describe(contract).Arguments[0] == new SlotArgumentLocation("rcx", 0, 64) &&
                    MachineAbi.Describe(contract).Result == new SlotArgumentLocation("rax", 0, 64), "Windows small aggregate uses integer argument and result locations");
            var identity = new NirRecoveryChecks.FixtureSource(MachineAbi.ArchitectureFor(abi), "fixture:aggregate-identity");
            identity.Add(0x1000, arm ? ["C0035FD6"] : ["4889C8", "C3"]);
            foreach (var value in Cases(type.Width)) checks += Compare(identity, [contract], [value], value);

            var caller = new NirRecoveryChecks.FixtureSource(MachineAbi.ArchitectureFor(abi), "fixture:aggregate-call");
            if (arm)
            {
                caller.Add(0x1000, "FD7BBFA9", NirRecoveryChecks.ArmCall(0x1004, 0x1100), "FD7BC1A8", "C0035FD6");
                caller.Add(0x1100, "00040091", "21080091", "C0035FD6");
            }
            else
            {
                caller.Add(0x1000, "4883EC28", NirRecoveryChecks.X64Call(0x1004, 0x1100), "4883C428", "C3");
                caller.Add(0x1100, "488D4101", "C3");
            }
            var callee = contract with { Name = "increment", EntryAddress = 0x1100 };
            foreach (var value in Cases(type.Width))
            {
                var expected = ((value + 1) & MirInterpreter.Mask(64)) |
                    (arm ? (((value >> 64) + 2) & MirInterpreter.Mask(64)) << 64 : BigInteger.Zero);
                checks += Compare(caller, [contract, callee], [value], expected);
            }
            var tail = new NirRecoveryChecks.FixtureSource(MachineAbi.ArchitectureFor(abi), "fixture:aggregate-tail");
            tail.Add(0x1000, arm ? "40000014" : "E9FB000000");
            tail.Add(0x1100, arm ? ["C0035FD6"] : ["4889C8", "C3"]);
            var independentCallee = JsonSerializer.Deserialize<FunctionContract>(JsonSerializer.Serialize(callee))!;
            var tailResult = NirRecoveryChecks.Recover(tail, [contract, independentCallee]);
            Check(tailResult.Complete && tailResult.Module.Functions.Single(function => function.Id == "identity").Blocks
                .Any(block => block.Terminator is NirTailCall), "structurally equal independent aggregate contracts permit a proven tail call");
            checks += Compare(tail, [contract, independentCallee], [123], 123);

            var padded = new RecoveryScalarType(64, RecoveryScalarKind.Aggregate,
                new(4, [new(0, new(8)), new(4, new(32))]));
            var overlap = new RecoveryScalarType(64, RecoveryScalarKind.Aggregate,
                new(4, [new(0, new(32)), new(0, new(32))]));
            Check(!MachineAbi.TryDescribe(contract with { Signature = new([padded], padded) }, out _, out _), "padding never acquires invented logical bits");
            Check(!MachineAbi.TryDescribe(contract with { Signature = new([overlap], overlap) }, out _, out _), "overlapping fields require a separate representation contract");
            var packed = Aggregate(1, new(32, RecoveryScalarKind.Float), new(32, RecoveryScalarKind.Float));
            var nestedPacked = Aggregate(4, packed);
            var misaligned = Aggregate(1, new(8), new(32));
            var nonstandardLeaf = Aggregate(1, new(24), new(8));
            foreach (var unsupported in new[] { packed, nestedPacked, misaligned, nonstandardLeaf })
                Check(!MachineAbi.TryDescribe(contract with { Signature = new([unsupported], null) }, out _, out _),
                    "packed, nested packed, unaligned and unknown scalar-alignment layouts remain explicit gaps");
            var reference = Aggregate(8, new RecoveryScalarType(64, RecoveryScalarKind.Address));
            Check(MachineAbi.TryDescribe(contract with { Signature = new([reference], reference) }, out _, out _),
                "natural address members retain by-value aggregate support");
            var indirect = Aggregate(8, U64, U64, U64);
            Check(!MachineAbi.TryDescribe(contract with { Signature = new([indirect], type) }, out _, out var argumentReason) && argumentReason!.Contains("间接"),
                "large argument remains an explicit indirect-storage gap");
            Check(!MachineAbi.TryDescribe(contract with { Signature = new([type], indirect) }, out _, out var returnReason) && returnReason!.Contains("隐藏"),
                "hidden return storage is not mistaken for an ordinary pointer result");
        }

        var armIdentity = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:aggregate-hfa");
        armIdentity.Add(0x1000, "C0035FD6");
        var floatThree = Aggregate(4, new(32, RecoveryScalarKind.Float), new(32, RecoveryScalarKind.Float), new(32, RecoveryScalarKind.Float));
        foreach (var type in new[] { Hfa, floatFour, floatThree, narrowPair })
        foreach (var value in Cases(type.Width))
            checks += Compare(armIdentity, [pair with { Signature = new([type], type) }], [value], value);
        var hfaCaller = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:hfa-call");
        hfaCaller.Add(0x1000, "FD7BBFA9", NirRecoveryChecks.ArmCall(0x1004, 0x1100), "FD7BC1A8", "C0035FD6");
        hfaCaller.Add(0x1100, "C0035FD6");
        foreach (var type in new[] { Hfa, floatFour, floatThree })
        {
            var callerContract = pair with { Signature = new([type], type) };
            foreach (var value in Cases(type.Width))
                checks += Compare(hfaCaller, [callerContract, callerContract with { Name = "hfa_callee", EntryAddress = 0x1100 }], [value], value);
        }
        var naturalSource = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:aggregate-natural-register");
        naturalSource.Add(0x1000, "E00301AA", "E10302AA", "C0035FD6");
        checks += Compare(naturalSource, [naturalContract], [13, (BigInteger.One << 100) + 7, 19], (BigInteger.One << 100) + 7);
        var spillSource = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:aggregate-stack");
        spillSource.Add(0x1000, "E00340F9", "E10740F9", "C0035FD6");
        checks += Compare(spillSource, [spillContract], [1, 2, 3, 4, 5, 6, 7, (BigInteger.One << 127) + 91, 9], (BigInteger.One << 127) + 91);
        var hfaSource = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:hfa-stack");
        hfaSource.Add(0x1000, "E00340FD", "E10740FD", "C0035FD6");
        checks += Compare(hfaSource, [hfaContract], [1, 2, 3, 4, 5, 6, 7, (BigInteger.One << 126) + 99, 9, 10], (BigInteger.One << 126) + 99);
        var naturalHfaSource = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:hfa-natural-stack");
        naturalHfaSource.Add(0x1000, "E00B40FD", "C0035FD6");
        checks += Compare(naturalHfaSource, [naturalHfaSpill], [1, 2, 3, 4, 5, 6, 7, 8, 9, (BigInteger.One << 126) + 99], BigInteger.One << 62);
        var stackCaller = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:aggregate-stack-call");
        stackCaller.Add(0x1000, "FF8300D1", "FD7B01A9", "E81340F9", "E80300F9", "E81740F9", "E80700F9",
            NirRecoveryChecks.ArmCall(0x1018, 0x1100), "FD7B41A9", "FF830091", "C0035FD6");
        stackCaller.Add(0x1100, "E00340F9", "E10740F9", "C0035FD6");
        var stackSignature = new FunctionSignature(spillArguments.RemoveAt(8), Pair);
        var stackContract = pair with { Signature = stackSignature };
        checks += Compare(stackCaller, [stackContract, stackContract with { Name = "stack_callee", EntryAddress = 0x1100 }],
            [1, 2, 3, 4, 5, 6, 7, (BigInteger.One << 90) + 73], (BigInteger.One << 90) + 73);
        var overwritten = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:aggregate-stack-clobber");
        overwritten.Add(0x1000, "FF8300D1", "FD7B01A9", "E81340F9", "E80300F9", "E81740F9", "E80700F9",
            NirRecoveryChecks.ArmCall(0x1018, 0x1100), "E00740F9", "FD7B41A9", "FF830091", "C0035FD6");
        overwritten.Add(0x1100, "C0035FD6");
        var scalarCaller = stackContract with { Signature = stackContract.Signature with { Result = U64 } };
        var voidCallee = stackContract with { Name = "may_clobber", EntryAddress = 0x1100,
            Signature = stackContract.Signature with { Result = null } };
        var clobbered = NirRecoveryChecks.Recover(overwritten, [scalarCaller, voidCallee]);
        Check(!clobbered.Functions.Single(function => function.Graph.Contract.Name == "pair").Complete &&
            clobbered.Functions.SelectMany(function => function.Diagnostics).Any(diagnostic => diagnostic.Code == "frame.uninitialized"),
            "callee ownership invalidates the second eight-byte half of a stack aggregate even for pure calls");
        var unsafeTail = new NirRecoveryChecks.FixtureSource(Architecture.Arm64, "fixture:aggregate-tail-capacity");
        unsafeTail.Add(0x1000, "40000014");
        unsafeTail.Add(0x1100, "E00340F9", "E10740F9", "C0035FD6");
        var shortCaller = pair with { Signature = new(Enumerable.Repeat(U64, 9).ToImmutableArray(), Pair) };
        var largerCallee = stackContract with { Name = "larger_tail", EntryAddress = 0x1100 };
        var tooSmall = NirRecoveryChecks.Recover(unsafeTail, [shortCaller, largerCallee]);
        Check(!tooSmall.Functions.Single(function => function.Graph.Contract.Name == "pair").Complete &&
            tooSmall.Functions.SelectMany(function => function.Diagnostics).Any(diagnostic => diagnostic.Code == "tail.stack-capacity"),
            "tail proof rejects a sixteen-byte aggregate when the caller guarantees only eight stack bytes");
        return checks;
    }

    private static RecoveryScalarType Aggregate(int alignment, params RecoveryScalarType[] fields)
    {
        var offset = 0;
        return new(fields.Sum(field => field.Width), RecoveryScalarKind.Aggregate, new(alignment, fields.Select(type =>
        { var field = new RecoveryAggregateField(offset, type); offset += type.Width / 8; return field; }).ToImmutableArray()));
    }

    private static FunctionContract Contract(MachineAbiKind abi, string name, ulong address,
        ImmutableArray<RecoveryScalarType> arguments, RecoveryScalarType result) =>
        new(name, address, new(arguments, result), abi, new(false, false, false, false, true, false, false),
            ["fixed-layout plain-data aggregate; field offsets and ABI are fixture evidence"], new(true, true, true, true));

    private static IEnumerable<BigInteger> Cases(int width) => new BigInteger[]
        { 0, 1, MirInterpreter.Mask(width), BigInteger.One << (width - 1), (BigInteger.One << (width / 2)) + 17 };

    private static int Compare(NirRecoveryChecks.FixtureSource source, FunctionContract[] contracts,
        BigInteger[] arguments, BigInteger expected)
    {
        var recovered = NirRecoveryChecks.Recover(source, contracts);
        CoreChecks.Require(recovered.Complete, NirRecoveryChecks.Explain(recovered));
        var module = NirJson.Deserialize(NirJson.Serialize(recovered.Module));
        var contract = contracts[0];
        var mapping = MachineAbi.Describe(contract);
        var state = NirRecoveryChecks.InitialState(source.Architecture, [], source.Addresses);
        var entrySp = (ulong)state.Slots[mapping.StackPointer];
        for (var index = 0; index < arguments.Length; index++)
        foreach (var part in MachineAbi.Pieces(mapping.Arguments[index]))
        {
            var value = (arguments[index] >> part.ValueBitOffset) & MirInterpreter.Mask(part.Location.Width);
            if (part.Location is SlotArgumentLocation slot) state.Slots[slot.Slot] =
                (state.Slots[slot.Slot] & ~(MirInterpreter.Mask(slot.Width) << slot.Offset)) | (value << slot.Offset);
            else if (part.Location is StackArgumentLocation saved)
                for (var offset = 0; offset < (saved.Width + 7) / 8; offset++)
                    state.Memory[entrySp + (ulong)saved.EntrySpOffset + (ulong)offset] = (byte)((value >> (offset * 8)) & 255);
        }
        NirRecoveryChecks.ExecuteMachine(source, contract.EntryAddress, state);
        var actual = BigInteger.Zero;
        foreach (var part in MachineAbi.Pieces(mapping.Result!))
        {
            var slot = (SlotArgumentLocation)part.Location;
            actual |= ((state.Slots[slot.Slot] >> slot.Offset) & MirInterpreter.Mask(slot.Width)) << part.ValueBitOffset;
        }
        var nir = NirInterpreter.Execute(module, contract.Name, arguments.Select((value, index) =>
            NirRuntimeValue.Integer(contract.Signature.Arguments[index].Width, value)).ToImmutableArray());
        CoreChecks.Require(nir.Status == NirExecutionStatus.Returned && nir.Values.Length == 1 && nir.Values[0].Bits == expected && actual == expected,
            $"{source.ImageId}: MIR and detached NIR agree with independent aggregate expectation");
        CoreChecks.Require(state.Slots[mapping.StackPointer] == entrySp + (ulong)mapping.NormalReturnSpAdjustment,
            "aggregate machine fixture executes the complete return protocol");
        return 3;
    }
}
