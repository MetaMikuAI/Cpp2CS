using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Validation;

public static class NirAtomicRecoveryChecks
{
    private const ulong Entry = NirRecoveryChecks.Entry;
    private const ulong Address = 0x500000;

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        var mask = (BigInteger.One << 64) - 1;
        var codes = new[]
        {
            ("F0480111", NirAtomicCode.Add), ("F0482911", NirAtomicCode.Sub),
            ("F0482111", NirAtomicCode.And), ("F0480911", NirAtomicCode.Or),
            ("F0483111", NirAtomicCode.Xor), ("F048F719", NirAtomicCode.Neg),
            ("F048F711", NirAtomicCode.Not)
        };
        foreach (var (encoding, code) in codes)
        {
            var source = Source(Architecture.X64, encoding, "488B01", "C3");
            var contract = Contract(Architecture.X64, "atomic_" + code, 2);
            var recovered = Recover(source, contract);
            var operation = recovered.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).OfType<NirAtomicRmw>().Single();
            Check(operation.Code == code && operation.MemoryOrder == NirMemoryOrder.SequentiallyConsistent,
                "locked arithmetic preserves neutral atomic opcode and ordering");
            foreach (var initial in new BigInteger[] { 0, 1, ulong.MaxValue, BigInteger.One << 63 })
            {
                var operand = new BigInteger(7);
                var expected = (code switch
                {
                    NirAtomicCode.Add => initial + operand, NirAtomicCode.Sub => initial - operand,
                    NirAtomicCode.And => initial & operand, NirAtomicCode.Or => initial | operand,
                    NirAtomicCode.Xor => initial ^ operand, NirAtomicCode.Neg => -initial,
                    NirAtomicCode.Not => ~initial, _ => throw new InvalidOperationException("unexpected fixture atomic code")
                }) & mask;
                checks += Compare(source, recovered.Module, contract.Name, [Address, operand], initial, expected, expected);
            }
        }
        foreach (var encoding in new[] { "488711", "F0480FC111" })
        {
            var source = Source(Architecture.X64, encoding, "4889D0", "C3");
            var contract = Contract(Architecture.X64, encoding == "488711" ? "exchange" : "fetch_add", 2);
            var recovered = Recover(source, contract);
            Check(recovered.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).OfType<NirAtomicRmw>().Count() == 1,
                "exchange and fetch-add retain one atomic read-modify-write operation");
            checks += Compare(source, recovered.Module, contract.Name, [Address, 19], 7, 7, encoding == "488711" ? 19 : 26);
        }
        var casSource = Source(Architecture.X64, "4C89C0", "F0480FB111", "C3");
        var casContract = Contract(Architecture.X64, "compare_exchange", 3);
        var cas = Recover(casSource, casContract);
        var compare = cas.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).OfType<NirCompareExchange>().Single();
        Check(compare.OldValue.Type == new NirBitsType(64) && compare.Success.Type == new NirBitsType(1) &&
            compare.SuccessOrder == NirMemoryOrder.SequentiallyConsistent && compare.FailureOrder == NirMemoryOrder.SequentiallyConsistent &&
            compare.WriteBackOnFailure, "x64 CAS preserves old-value result, success flag, failure ordering and writeback");
        foreach (var expected in new BigInteger[] { 7, 8 })
            checks += Compare(casSource, cas.Module, casContract.Name, [Address, 19, expected], 7, 7, expected == 7 ? 19 : 7);

        var successSource = Source(Architecture.X64, "4C89C0", "F0480FB111", "0F94C0", "0FB6C0", "C3");
        var successContract = Contract(Architecture.X64, "compare_exchange_success", 3);
        var success = Recover(successSource, successContract);
        foreach (var expected in new BigInteger[] { 7, 8 })
            checks += Compare(successSource, success.Module, successContract.Name, [Address, 19, expected], 7,
                expected == 7 ? 1 : 0, expected == 7 ? 19 : 7);

        var load = Source(Architecture.Arm64, "00FCDFC8", "C0035FD6");
        var loadContract = Contract(Architecture.Arm64, "acquire_load", 1);
        var loadResult = Recover(load, loadContract);
        Check(loadResult.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).OfType<NirLoad>()
            .Any(operation => operation.MemoryOrder == NirMemoryOrder.Acquire && operation.AtomicWidth == 64),
            "ARM LDAR preserves acquire order and 64-bit atomic width");
        checks += Compare(load, loadResult.Module, loadContract.Name, [Address], 27, 27, 27);
        var store = Source(Architecture.Arm64, "01FC9FC8", "E00301AA", "C0035FD6");
        var storeContract = Contract(Architecture.Arm64, "release_store", 2);
        var storeResult = Recover(store, storeContract);
        Check(storeResult.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).OfType<NirStore>()
            .Any(operation => operation.MemoryOrder == NirMemoryOrder.Release && operation.AtomicWidth == 64),
            "ARM STLR preserves release order and 64-bit atomic width");
        checks += Compare(store, storeResult.Module, storeContract.Name, [Address, 37], 27, 37, 37);

        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var arm = architecture == Architecture.Arm64;
            var fences = arm ? new[] { "BF3F03D5", "BF3D03D5", "BF3E03D5" } : ["0FAEF0", "0FAEE8", "0FAEF8"];
            var orders = new[] { NirMemoryOrder.SequentiallyConsistent, NirMemoryOrder.Acquire, NirMemoryOrder.Release };
            for (var index = 0; index < fences.Length; index++)
            {
                var source = Source(architecture, fences[index], arm ? "E00301AA" : "4889D0", arm ? "C0035FD6" : "C3");
                var contract = Contract(architecture, "fence_" + index, 2);
                var recovered = Recover(source, contract);
                Check(recovered.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).OfType<NirFence>()
                    .Single().MemoryOrder == orders[index], "full-system fence preserves its supported neutral ordering event");
                checks += Compare(source, recovered.Module, contract.Name, [Address, 53], 11, 53, 11);
            }
        }
        foreach (var barrier in new[] { "9F3F03D5", "DF3F03D5", "BF3B03D5" })
        {
            var source = Source(Architecture.Arm64, barrier, "E00301AA", "C0035FD6");
            var result = NirRecovery.Recover(source, [Contract(Architecture.Arm64, "unmapped_barrier", 2)]);
            Check(!result.Complete && result.Gaps.Any(gap => gap.Code == "memory.barrier"),
                "DSB, ISB and narrower shareability domains remain explicit recovery gaps");
        }
        var exclusive = Source(Architecture.Arm64, "007C5FC8", "C0035FD6");
        var exclusiveResult = NirRecovery.Recover(exclusive, [Contract(Architecture.Arm64, "exclusive", 1)]);
        Check(!exclusiveResult.Complete && exclusiveResult.Gaps.Any(gap => gap.Code == "memory.exclusive"),
            "load-exclusive does not expose its machine monitor as an NIR input");
        var privateAtomic = Source(Architecture.Arm64, "FF4300D1", "E0FF9FC8", "FF430091", "C0035FD6");
        var privateResult = NirRecovery.Recover(privateAtomic, [Contract(Architecture.Arm64, "private_atomic", 1)]);
        Check(!privateResult.Complete && privateResult.Gaps.Any(gap => gap.Code == "memory.atomic-frame"),
            "atomic store on a private frame is not deleted as dead protocol storage");
        var missingDomain = NirRecovery.Recover(casSource,
            [casContract with { Domain = casContract.Domain! with { NormalExecution = false } }]);
        Check(!missingDomain.Complete && missingDomain.Gaps.Any(gap => gap.Code == "memory.atomic-address"),
            "atomic conversion requires an explicit normal machine-address domain");
        var missingEffects = NirRecovery.Recover(casSource,
            [casContract with { Effects = casContract.Effects with { WritesMemory = false } }]);
        Check(!missingEffects.Complete && missingEffects.Gaps.Any(gap => gap.Code == "contract.memory-effects"),
            "atomic write cannot exceed the declared function effects");
        return checks;
    }

    private static NirRecoveryChecks.FixtureSource Source(Architecture architecture, params string[] encodings)
    {
        var source = new NirRecoveryChecks.FixtureSource(architecture, "fixture:nir-atomic-recovery");
        source.Add(Entry, encodings);
        return source;
    }

    private static FunctionContract Contract(Architecture architecture, string name, int arguments) => new(name, Entry,
        new(Enumerable.Range(0, arguments).Select(index => new RecoveryScalarType(64,
            index == 0 ? RecoveryScalarKind.Address : RecoveryScalarKind.Integer)).ToImmutableArray(), new(64)),
        architecture == Architecture.Arm64 ? MachineAbiKind.Aapcs64 : MachineAbiKind.WindowsX64,
        new(true, true, true, false, true, false, false),
        ["handwritten binary fixture interface; address and ordered-memory assumptions are explicit"], new(true, true, true, true));

    private static NirRecoveryResult Recover(NirRecoveryChecks.FixtureSource source, FunctionContract contract)
    {
        var result = NirRecovery.Recover(source, [contract]);
        CoreChecks.Require(result.Complete, NirRecoveryChecks.Explain(result));
        var serialized = NirJson.Serialize(result.Module);
        var detached = NirJson.Deserialize(serialized);
        CoreChecks.Require(NirValidator.Validate(detached).IsValid && NirJson.Serialize(detached) == serialized,
            "atomic recovered module validates after stable JSON round trip");
        return result with { Module = detached };
    }

    private static int Compare(NirRecoveryChecks.FixtureSource source, NirModule module, string function,
        BigInteger[] arguments, BigInteger initial, BigInteger expectedReturn, BigInteger expectedMemory)
    {
        var state = NirRecoveryChecks.InitialState(source.Architecture, arguments, source.Addresses);
        var bytes = Enumerable.Range(0, 8).Select(index => (byte)((initial >> (index * 8)) & 255)).ToArray();
        for (var index = 0; index < bytes.Length; index++)
        {
            state.Memory[Address + (ulong)index] = bytes[index];
            state.WritePermissions[Address + (ulong)index] = true;
        }
        var machine = NirRecoveryChecks.ExecuteMachine(source, Entry, state);
        var context = new NirExecutionContext(module);
        CoreChecks.Require(context.Memory.Map(new("memory", Address, 8, true), [.. bytes]) is null,
            "atomic recovery fixture provides mapped writable program bytes");
        var input = arguments.Select((argument, index) => index == 0 ? NirRuntimeValue.Address("memory", 64, argument)
            : NirRuntimeValue.Integer(64, argument)).ToImmutableArray();
        var nir = NirInterpreter.Execute(module, function, input, context);
        CoreChecks.Require(nir.Status == NirExecutionStatus.Returned && nir.Values.Length == 1 &&
            nir.Values[0].Bits == machine.Result && machine.Result == expectedReturn,
            $"atomic complete MIR+RET/NIR return: {function}: {nir.Status}: {nir.Detail}");
        var expectedBytes = Enumerable.Range(0, 8).Select(index => (byte)((expectedMemory >> (index * 8)) & 255)).ToArray();
        CoreChecks.Require(expectedBytes.SequenceEqual(Enumerable.Range(0, 8).Select(index => state.Memory[Address + (ulong)index])) &&
            context.Memory.Read("memory", Address, 8).Bytes.SequenceEqual(expectedBytes),
            "atomic complete MIR/NIR program-memory result agrees with the independent arithmetic expectation");
        var machineAtomic = state.Events.Where(item => item.Kind == "AtomicRmw").ToArray();
        var nirAtomic = nir.Events.Where(item => item.Memory?.AtomicWidth == 64 && item.Memory.ReadValue is not null && item.Memory.WrittenValue is not null).ToArray();
        CoreChecks.Require(machineAtomic.Length == nirAtomic.Length, "atomic read-modify-write observation count is preserved");
        for (var index = 0; index < machineAtomic.Length; index++)
        {
            CoreChecks.Require(nirAtomic[index].Memory!.Address == machineAtomic[index].Address &&
                nirAtomic[index].Memory!.Order == NirMemoryOrder.SequentiallyConsistent &&
                nirAtomic[index].Memory!.ReadValue == initial && nirAtomic[index].Memory!.WrittenValue == expectedMemory,
                "atomic observation preserves address, old value, writeback and ordering on both CAS outcomes");
        }
        return 4 + machineAtomic.Length;
    }
}
