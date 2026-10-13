using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Nir;

namespace Cpp2CS.Validation;

public static class NirAtomicChecks
{
    private static readonly NirAddressType AddressType = new("data", 16);
    private static void Require(bool condition, string label)
    {
        if (!condition) throw new InvalidOperationException("NIR atomic check failed: " + label);
    }
    private static NirModule Module(NirFunction function, params NirDataObject[] data) =>
        new([function], [], [new("data", 16, 0xf000, 0x1000)], [.. data]);
    private static NirDataObject Data(params byte[] bytes) => new("initial", "data", 0x100, [.. bytes], true);
    private static NirFunction Rmw(NirAtomicCode code, int width, NirByteOrder order = NirByteOrder.Little)
    {
        var address = new NirValue(new(0), AddressType); var operand = NirValue.Bits(1, width); var e = NirValue.Effect(2);
        var result = NirValue.Bits(3, width); var done = NirValue.Effect(4);
        return new("rmw", new([address.Type, operand.Type], [result.Type]), new(0), [new(new(0), [address, operand, e],
            [new NirAtomicRmw(result, address, operand, code, order, NirMemoryOrder.SequentiallyConsistent, new(e, done))], new NirReturn([result], done))]);
    }
    private static NirFunction Cas(bool writeBack = false)
    {
        var address = new NirValue(new(0), AddressType); var expected = NirValue.Bits(1, 32); var replacement = NirValue.Bits(2, 32); var e = NirValue.Effect(3);
        var old = NirValue.Bits(4, 32); var success = NirValue.Bits(5, 1); var done = NirValue.Effect(6);
        return new("cas", new([address.Type, expected.Type, replacement.Type], [old.Type, success.Type]), new(0), [new(new(0), [address, expected, replacement, e],
            [new NirCompareExchange(old, success, address, expected, replacement, NirByteOrder.Little, NirMemoryOrder.AcquireRelease, NirMemoryOrder.Acquire, new(e, done), writeBack)],
            new NirReturn([old, success], done))]);
    }
    public static int Run() => Arithmetic() + CompareExchange() + Ordering() + Failures() + Validation();

    private static int Arithmetic()
    {
        var checks = 0;
        foreach (var code in Enum.GetValues<NirAtomicCode>())
        foreach (var width in new[] { 8, 16, 32, 64, 128 })
        foreach (var order in Enum.GetValues<NirByteOrder>())
        {
            var previous = (BigInteger.One << width) - 3;
            var operand = new BigInteger(5);
            var data = NirAtomicContract.Bytes(previous, width, order);
            var module = Module(Rmw(code, width, order), Data(data.ToArray()));
            Require(NirValidator.Validate(module).IsValid, $"rmw graph {code}/{width}/{order}");
            var restored = NirJson.Deserialize(NirJson.Serialize(module));
            var context = new NirExecutionContext(restored);
            var result = NirInterpreter.Execute(restored, "rmw", [NirRuntimeValue.Address("data", 16, 0x100), NirRuntimeValue.Integer(width, operand)], context);
            var expected = (code switch
            {
                NirAtomicCode.Exchange => operand, NirAtomicCode.Add => previous + operand, NirAtomicCode.Sub => previous - operand,
                NirAtomicCode.And => previous & operand, NirAtomicCode.Or => previous | operand, NirAtomicCode.Xor => previous ^ operand,
                NirAtomicCode.Neg => -previous, NirAtomicCode.Not => ~previous, _ => throw new InvalidOperationException()
            }) & ((BigInteger.One << width) - 1);
            Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == previous, "rmw returns old value");
            Require(context.Memory.Read("data", 0x100, width / 8).Bytes.SequenceEqual(NirAtomicContract.Bytes(expected, width, order)), "rmw commits wrapped result");
            Require(result.Events.Length == 1 && result.Events[0].Memory is { Order: NirMemoryOrder.SequentiallyConsistent } memory &&
                memory.Width == width && memory.AtomicWidth == width && memory.ReadValue == previous && memory.WrittenValue == expected, "rmw atomic event");
            checks += 4;
        }
        return checks;
    }
    private static int CompareExchange()
    {
        var checks = 0;
        foreach (var writeBack in new[] { false, true })
        foreach (var match in new[] { false, true })
        {
            var module = Module(Cas(writeBack), Data(42, 0, 0, 0));
            var json = NirJson.Serialize(module);
            var restored = NirJson.Deserialize(json);
            Require(NirJson.Serialize(restored) == json && NirValidator.Validate(restored).IsValid, "cas JSON roundtrip");
            var context = new NirExecutionContext(restored);
            var result = NirInterpreter.Execute(restored, "cas", [NirRuntimeValue.Address("data", 16, 0x100), NirRuntimeValue.Integer(32, match ? 42 : 41), NirRuntimeValue.Integer(32, 100)], context);
            Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 42 && result.Values[1].Bits == (match ? 1 : 0), "cas result and success");
            Require(context.Memory.Read("data", 0x100, 4).Bytes[0] == (match ? 100 : 42), "cas replacement");
            Require(result.Events[0].Memory is { } memory && memory.ExchangeSucceeded == match && memory.ReadValue == 42 &&
                memory.WrittenValue == (match ? new BigInteger(100) : writeBack ? new BigInteger(42) : null) &&
                memory.Order == (match ? NirMemoryOrder.AcquireRelease : NirMemoryOrder.Acquire), "cas branch order and writeback event");
            Require(context.Memory.Writes == (match || writeBack ? 1 : 0), "cas exact write count");
            checks += 5;
        }
        return checks;
    }
    private static int Ordering()
    {
        var address = new NirValue(new(0), AddressType); var value = NirValue.Bits(1, 32); var e0 = NirValue.Effect(2);
        var e1 = NirValue.Effect(3); var e2 = NirValue.Effect(4); var e3 = NirValue.Effect(5); var read = NirValue.Bits(6, 32);
        var function = new NirFunction("ordered", new([address.Type, value.Type], [read.Type]), new(0), [new(new(0), [address, value, e0],
            [new NirStore(address, value, NirByteOrder.Little, new(e0, e1), NirMemoryOrder.Release, 16),
             new NirFence(NirMemoryOrder.SequentiallyConsistent, new(e1, e2)),
             new NirLoad(read, address, NirByteOrder.Little, new(e2, e3), NirMemoryOrder.Acquire, 16)], new NirReturn([read], e3))]);
        var module = Module(function, Data(0, 0, 0, 0));
        Require(NirValidator.Validate(module).IsValid, "ordered graph");
        var restored = NirJson.Deserialize(NirJson.Serialize(module));
        var result = NirInterpreter.Execute(restored, "ordered", [NirRuntimeValue.Address("data", 16, 0x100), NirRuntimeValue.Integer(32, 0x12345678)]);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 0x12345678, "ordered readback");
        Require(result.Events.Length == 5 && result.Events.Select(x => x.Sequence).SequenceEqual(new long[] { 1, 2, 3, 4, 5 }), "each atomic beat and fence has distinct event");
        Require(result.Events.Select(x => x.Memory!.Order).SequenceEqual(new[] { NirMemoryOrder.Release, NirMemoryOrder.Release, NirMemoryOrder.SequentiallyConsistent, NirMemoryOrder.Acquire, NirMemoryOrder.Acquire }), "event order contracts");
        Require(result.Events[0].Memory!.WrittenValue == 0x5678 && result.Events[1].Memory!.WrittenValue == 0x1234 &&
            result.Events[3].Memory!.ReadValue == 0x5678 && result.Events[4].Memory!.ReadValue == 0x1234, "beat addresses and values");
        Require(NirText.Format(restored).Contains("fence.SequentiallyConsistent", StringComparison.Ordinal), "readable order");
        return 6;
    }
    private static int Failures()
    {
        var initial = new NirDataObject("initial", "data", 0x100, [1, 2], true);
        var protectedBytes = new NirDataObject("protected", "data", 0x102, [3, 4], false);
        var module = Module(Rmw(NirAtomicCode.Add, 32), initial, protectedBytes);
        var context = new NirExecutionContext(module);
        var result = NirInterpreter.Execute(module, "rmw", [NirRuntimeValue.Address("data", 16, 0x100), NirRuntimeValue.Integer(32, 0xffffffff)], context);
        Require(result.Status == NirExecutionStatus.Faulted && result.Detail == "WritePermissionFault", "rmw permission fault");
        Require(context.Memory.Read("data", 0x100, 4).Bytes.SequenceEqual(new byte[] { 1, 2, 3, 4 }) && context.Memory.Writes == 0, "failed rmw cannot partially write");
        Require(result.Events.Length == 1 && result.Events[0].Memory is { WrittenValue: null, ReadValue: null }, "failed atomic has no result event");
        module = Module(Cas(), initial, protectedBytes);
        context = new(module);
        result = NirInterpreter.Execute(module, "cas", [NirRuntimeValue.Address("data", 16, 0x100), NirRuntimeValue.Integer(32, 0), NirRuntimeValue.Integer(32, 9)], context);
        Require(result.Status == NirExecutionStatus.Faulted && context.Memory.Writes == 0, "failed comparison still requires whole write permission");
        module = Module(Rmw(NirAtomicCode.Exchange, 32));
        context = new(module);
        Require(context.Memory.Map(new("data", 0x100, 4, true), [1, 2]) is null, "partial initial input");
        result = NirInterpreter.Execute(module, "rmw", [NirRuntimeValue.Address("data", 16, 0x100), NirRuntimeValue.Integer(32, 9)], context);
        Require(result.Status == NirExecutionStatus.MissingInput && context.Memory.Writes == 0, "uninitialized atomic does not fabricate previous value");

        var address = new NirValue(new(0), AddressType); var value = NirValue.Bits(1, 32); var e = NirValue.Effect(2); var done = NirValue.Effect(3);
        var function = new NirFunction("store", new([address.Type, value.Type], []), new(0), [new(new(0), [address, value, e],
            [new NirStore(address, value, NirByteOrder.Little, new(e, done), NirMemoryOrder.Release, 16)], new NirReturn([], done))]);
        module = Module(function, initial, protectedBytes);
        context = new(module);
        result = NirInterpreter.Execute(module, "store", [NirRuntimeValue.Address("data", 16, 0x100), NirRuntimeValue.Integer(32, 0x11223344)], context);
        Require(result.Status == NirExecutionStatus.Faulted && result.Events.Length == 2, "later beat fault remains distinct");
        Require(context.Memory.Read("data", 0x100, 4).Bytes.SequenceEqual(new byte[] { 0x44, 0x33, 3, 4 }), "earlier atomic store beat remains committed");

        module = Module(Rmw(NirAtomicCode.Add, 32), new("tail", "data", 65534, [0xff, 0xff], true), new("head", "data", 0, [0xff, 0xff], true)) with
        { MemorySpaces = [new("data", 16, 0, 0)] };
        context = new(module);
        result = NirInterpreter.Execute(module, "rmw", [NirRuntimeValue.Address("data", 16, 65534), NirRuntimeValue.Integer(32, 1)], context);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == uint.MaxValue &&
            context.Memory.Read("data", 65534, 4).Bytes.All(x => x == 0), "single atomic granule supports modular boundary crossing");
        return 9;
    }
    private static int Validation()
    {
        var checks = 0;
        var function = Cas();
        var operation = (NirCompareExchange)function.Blocks[0].Operations[0];
        foreach (var pair in new[] { (NirMemoryOrder.Relaxed, NirMemoryOrder.Acquire), (NirMemoryOrder.Release, NirMemoryOrder.Acquire),
                     (NirMemoryOrder.SequentiallyConsistent, NirMemoryOrder.Release), (NirMemoryOrder.Acquire, NirMemoryOrder.SequentiallyConsistent) })
        {
            var bad = function with { Blocks = [function.Blocks[0] with { Operations = [operation with { SuccessOrder = pair.Item1, FailureOrder = pair.Item2 }] }] };
            Require(!NirValidator.Validate(Module(bad)).IsValid, "invalid compare failure order");
            checks++;
        }
        var stale = function with { Blocks = [function.Blocks[0] with { Terminator = new NirReturn([operation.OldValue, operation.Success], operation.Flow.Input) }] };
        Require(!NirValidator.Validate(Module(stale)).IsValid, "atomic Effect must remain current");
        var noFault = function with { Outcomes = NirOutcomes.Return };
        Require(!NirValidator.Validate(Module(noFault)).IsValid, "atomic fault outcome required");
        var address = new NirValue(new(0), AddressType); var e = NirValue.Effect(1); var done = NirValue.Effect(2); var read = NirValue.Bits(3, 32);
        foreach (var load in new[] { new NirLoad(read, address, NirByteOrder.Little, new(e, done), NirMemoryOrder.Release, 32),
                     new NirLoad(read, address, NirByteOrder.Little, new(e, done), NirMemoryOrder.Acquire, 0),
                     new NirLoad(read, address, NirByteOrder.Little, new(e, done), NirMemoryOrder.Relaxed, 24) })
        {
            var bad = new NirFunction("load", new([address.Type], [read.Type]), new(0), [new(new(0), [address, e], [load], new NirReturn([read], done))]);
            Require(!NirValidator.Validate(Module(bad)).IsValid, "invalid load order or granule");
            checks++;
        }
        var fence = new NirFunction("fence", new([], []), new(0), [new(new(0), [e], [new NirFence(NirMemoryOrder.Relaxed, new(e, done))], new NirReturn([], done))]);
        Require(!NirValidator.Validate(Module(fence)).IsValid, "relaxed fence rejected");
        return checks + 3;
    }
}
