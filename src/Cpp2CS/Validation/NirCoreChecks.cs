using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Nir;

namespace Cpp2CS.Validation;

public static class NirCoreChecks
{
    private static readonly NirBitsType I32 = new(32);
    private static readonly NirSignature BinarySignature = new([I32, I32], [I32]);
    private static NirModule Module(params NirFunction[] functions) => new([.. functions], [], [], []);
    private static void Require(bool condition, string label)
    {
        if (!condition) throw new InvalidOperationException("NIR check failed: " + label);
    }
    private static NirFunction AddFunction(string name = "add")
    {
        var a = NirValue.Bits(0, 32); var b = NirValue.Bits(1, 32); var e = NirValue.Effect(2); var r = NirValue.Bits(3, 32);
        return new(name, BinarySignature, new(0), [new(new(0), [a, b, e], [new NirPure(r, NirPureCode.Add, [a, b])], new NirReturn([r], e))])
        { Outcomes = NirOutcomes.Return };
    }
    public static int Run()
    {
        var checks = Arithmetic() + Calls() + Recursion() + Loops() + Memory() + MemoryWrapping() + Validation();
        return checks;
    }

    private static int Arithmetic()
    {
        var checks = 0;
        foreach (var width in new[] { 1, 8, 32, 64, 128 })
        {
            var mask = (BigInteger.One << width) - 1;
            foreach (var code in new[] { NirPureCode.Add, NirPureCode.Sub, NirPureCode.Mul, NirPureCode.And, NirPureCode.Or, NirPureCode.Xor,
                         NirPureCode.UDiv, NirPureCode.SDiv, NirPureCode.Shl, NirPureCode.Shr, NirPureCode.Sar, NirPureCode.Eq, NirPureCode.Ult, NirPureCode.Slt })
            {
                var compare = code is NirPureCode.Eq or NirPureCode.Ult or NirPureCode.Slt;
                var a = NirValue.Bits(0, width); var b = NirValue.Bits(1, width); var e = NirValue.Effect(2); var r = NirValue.Bits(3, compare ? 1 : width);
                var function = new NirFunction("op", new([a.Type, b.Type], [r.Type]), new(0),
                    [new(new(0), [a, b, e], [new NirPure(r, code, [a, b])], new NirReturn([r], e))]) { Outcomes = NirOutcomes.Return };
                var module = Module(function);
                foreach (var x in new[] { BigInteger.Zero, BigInteger.One, mask, BigInteger.One << (width - 1) })
                foreach (var y in new[] { BigInteger.Zero, BigInteger.One, mask, new BigInteger(width) & mask })
                {
                    var sx = x >= (BigInteger.One << (width - 1)) ? x - (BigInteger.One << width) : x;
                    var sy = y >= (BigInteger.One << (width - 1)) ? y - (BigInteger.One << width) : y;
                    var expected = code switch
                    {
                        NirPureCode.Add => x + y, NirPureCode.Sub => x - y, NirPureCode.Mul => x * y,
                        NirPureCode.And => x & y, NirPureCode.Or => x | y, NirPureCode.Xor => x ^ y,
                        NirPureCode.UDiv => y == 0 ? 0 : x / y, NirPureCode.SDiv => y == 0 ? 0 : sx / sy,
                        NirPureCode.Shl => y >= width ? 0 : x * BigInteger.Pow(2, (int)y),
                        NirPureCode.Shr => y >= width ? 0 : x / BigInteger.Pow(2, (int)y),
                        NirPureCode.Sar => y >= width ? sx.Sign < 0 ? -1 : 0 : sx >> (int)y,
                        NirPureCode.Eq => x == y ? 1 : 0, NirPureCode.Ult => x < y ? 1 : 0,
                        NirPureCode.Slt => sx < sy ? 1 : 0,
                        _ => throw new InvalidOperationException()
                    };
                    var result = NirInterpreter.Execute(module, "op", [NirRuntimeValue.Integer(width, x), NirRuntimeValue.Integer(width, y)]);
                    Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == (expected & (compare ? 1 : mask)), $"{code}/{width}/{x}/{y}");
                    checks++;
                }
            }
        }
        return checks;
    }

    private static int Calls()
    {
        var a = NirValue.Bits(0, 32); var b = NirValue.Bits(1, 32); var e = NirValue.Effect(2);
        var r = NirValue.Bits(3, 32); var e1 = NirValue.Effect(4);
        var pointer = new NirValue(new(5), new NirFunctionType(BinarySignature, NirOutcomes.Return));
        var caller = new NirFunction("caller", BinarySignature, new(0), [new(new(0), [a, b, e],
            [new NirFunctionConstant(pointer, "add"), new NirCall(new NirIndirectTarget(pointer), [a, b], [r], new(e, e1))], new NirReturn([r], e1))])
        { Outcomes = NirOutcomes.Return };
        var tail = new NirFunction("tail", BinarySignature, new(0), [new(new(0), [a, b, e], [], new NirTailCall(new NirDirectTarget("caller"), [a, b], e))])
        { Outcomes = NirOutcomes.Return };
        var module = Module(AddFunction(), caller, tail);
        Require(NirValidator.Validate(module).IsValid, "call module validation");
        Require(!NirValidator.Validate(Module(AddFunction(), caller, tail with { Outcomes = NirOutcomes.Diverge })).IsValid,
            "returning tail call contradicts caller no-return contract");
        var result = NirInterpreter.Execute(module, "tail", [NirRuntimeValue.Integer(32, uint.MaxValue), NirRuntimeValue.Integer(32, 2)]);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 1, "direct tail and indirect call");
        var json = NirJson.Serialize(module);
        var restored = NirJson.Deserialize(json);
        Require(NirValidator.Validate(restored).IsValid && NirJson.Serialize(restored) == json, "NIR JSON round trip");
        Require(NirText.Format(restored).Contains("tailcall @caller", StringComparison.Ordinal), "readable tail call");
        var externalModule = module with { Functions = [caller], Externals = [new("add", BinarySignature, NirExternalEffects.None, NirOutcomes.Return)] };
        var missing = NirInterpreter.Execute(externalModule, "caller", [NirRuntimeValue.Integer(32, 3), NirRuntimeValue.Integer(32, 7)]);
        Require(missing.Status == NirExecutionStatus.MissingExternal, "missing external is not a successful zero result");
        var context = new NirExecutionContext(externalModule);
        context.Externals.Add("add", invocation => NirExternalResult.Returned(NirRuntimeValue.Integer(32, invocation.Arguments[0].Bits + invocation.Arguments[1].Bits)));
        Require(NirInterpreter.Execute(externalModule, "caller", [NirRuntimeValue.Integer(32, 3), NirRuntimeValue.Integer(32, 7)], context).Values[0].Bits == 10, "external contract execution");
        context.Externals["add"] = _ => new(NirExternalOutcome.Fault, [], "bad");
        Require(NirInterpreter.Execute(externalModule, "caller", [NirRuntimeValue.Integer(32, 3), NirRuntimeValue.Integer(32, 7)], context).Status == NirExecutionStatus.ContractViolation, "external outcome violation");
        var stop = new NirFunction("stop", new([], []), new(0), [new(new(0), [e], [], new NirNoReturnCall(new NirDirectTarget("exit"), [], e))]) { Outcomes = NirOutcomes.Terminate };
        var stopped = new NirModule([stop], [new("exit", new([], []), NirExternalEffects.Environment, NirOutcomes.Terminate)], [], []);
        var stopContext = new NirExecutionContext(stopped);
        stopContext.Externals.Add("exit", _ => new(NirExternalOutcome.Terminate, [], "exit"));
        Require(NirInterpreter.Execute(stopped, "stop", [], stopContext).Status == NirExecutionStatus.Terminated, "no-return call terminates");
        stopContext.Externals["exit"] = _ => NirExternalResult.Returned();
        Require(NirInterpreter.Execute(stopped, "stop", [], stopContext).Status == NirExecutionStatus.ContractViolation, "no-return contract rejects return");
        return 10;
    }

    private static int Loops()
    {
        var n = NirValue.Bits(0, 32); var e = NirValue.Effect(1); var zero = NirValue.Bits(2, 32);
        var i = NirValue.Bits(3, 32); var sum = NirValue.Bits(4, 32); var le = NirValue.Effect(5);
        var condition = NirValue.Bits(6, 1); var next = NirValue.Bits(7, 32); var one = NirValue.Bits(8, 32); var total = NirValue.Bits(9, 32);
        var answer = NirValue.Bits(10, 32); var endEffect = NirValue.Effect(11);
        var function = new NirFunction("sum", new([n.Type], [n.Type]), new(0),
        [
            new(new(0), [n, e], [new NirConstant(zero, 0)], new NirJump(new(new(1), [n, zero, e]))),
            new(new(1), [i, sum, le], [new NirPure(condition, NirPureCode.Eq, [i, zero])],
                new NirBranch(condition, new(new(3), [sum, le]), new(new(2), [le]))),
            new(new(2), [NirValue.Effect(12)], [new NirConstant(one, 1), new NirPure(next, NirPureCode.Sub, [i, one]), new NirPure(total, NirPureCode.Add, [sum, i])],
                new NirJump(new(new(1), [next, total, NirValue.Effect(12)]))),
            new(new(3), [answer, endEffect], [], new NirReturn([answer], endEffect))
        ]) { Outcomes = NirOutcomes.Return | NirOutcomes.Diverge };
        var module = Module(function);
        Require(NirValidator.Validate(module).IsValid, "loop SSA validates");
        var result = NirInterpreter.Execute(module, "sum", [NirRuntimeValue.Integer(32, 10)]);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 55, "loop block arguments execute");
        Require(NirInterpreter.Execute(module, "sum", [NirRuntimeValue.Integer(32, uint.MaxValue)], options: new(MaxSteps: 20)).Status == NirExecutionStatus.BudgetExceeded, "loop budget remains analysis stop");
        var same = new NirFunction("entries", new([n.Type], [n.Type]), new(0),
        [
            new(new(0), [n, e], [], new NirReturn([n], e)),
            new(new(1), [i, le], [], new NirReturn([i], le))
        ]) { AdditionalEntries = [new(1)], Outcomes = NirOutcomes.Return };
        Require(NirValidator.Validate(Module(same)).IsValid, "multiple external entries");
        Require(NirInterpreter.Execute(Module(same), "entries", [NirRuntimeValue.Integer(32, 19)], options: new(Entry: new(1))).Values[0].Bits == 19, "explicit additional entry executes");
        return 5;
    }

    private static int Recursion()
    {
        var n = NirValue.Bits(0, 32); var e = NirValue.Effect(1); var zero = NirValue.Bits(2, 32); var test = NirValue.Bits(3, 1);
        var baseEffect = NirValue.Effect(4); var recursiveEffect = NirValue.Effect(5); var one = NirValue.Bits(6, 32);
        var next = NirValue.Bits(7, 32); var returned = NirValue.Bits(8, 32); var callEffect = NirValue.Effect(9); var answer = NirValue.Bits(10, 32);
        var recursive = new NirFunction("recursive", new([I32], [I32]), new(0),
        [
            new(new(0), [n, e], [new NirConstant(zero, 0), new NirPure(test, NirPureCode.Eq, [n, zero])],
                new NirBranch(test, new(new(1), [e]), new(new(2), [e]))),
            new(new(1), [baseEffect], [], new NirReturn([zero], baseEffect)),
            new(new(2), [recursiveEffect],
                [new NirConstant(one, 1), new NirPure(next, NirPureCode.Sub, [n, one]),
                    new NirCall(new NirDirectTarget("recursive"), [next], [returned], new(recursiveEffect, callEffect)),
                    new NirPure(answer, NirPureCode.Add, [returned, one])], new NirReturn([answer], callEffect))
        ]) { Outcomes = NirOutcomes.Return | NirOutcomes.Diverge };
        var module = Module(recursive);
        Require(NirValidator.Validate(module).IsValid, "recursive SSA validates");
        Require(NirInterpreter.Execute(module, "recursive", [NirRuntimeValue.Integer(32, 50)]).Values[0].Bits == 50, "recursive results return through each call binding");
        Require(NirInterpreter.Execute(module, "recursive", [NirRuntimeValue.Integer(32, 50)], options: new(MaxDepth: 8)).Status == NirExecutionStatus.BudgetExceeded,
            "recursive depth limit is an analysis stop");
        var tail = recursive with
        {
            Id = "taildown",
            Blocks = recursive.Blocks.SetItem(2, recursive.Blocks[2] with
            {
                Operations = [new NirConstant(one, 1), new NirPure(next, NirPureCode.Sub, [n, one])],
                Terminator = new NirTailCall(new NirDirectTarget("taildown"), [next], recursiveEffect)
            })
        };
        var tailResult = NirInterpreter.Execute(Module(tail), "taildown", [NirRuntimeValue.Integer(32, 200)], options: new(MaxDepth: 1));
        Require(tailResult.Status == NirExecutionStatus.Returned && tailResult.Values[0].Bits == 0, "tail recursion does not accumulate frames");
        return 4;
    }

    private static int Memory()
    {
        var e = NirValue.Effect(0); var size = NirValue.Bits(1, 32); var address = new NirValue(new(2), new NirAddressType("memory", 64));
        var e1 = NirValue.Effect(3); var value = NirValue.Bits(4, 32); var e2 = NirValue.Effect(5); var loaded = NirValue.Bits(6, 32); var e3 = NirValue.Effect(7);
        var addressBits = NirValue.Bits(8, 64); var addressAgain = new NirValue(new(9), address.Type);
        var function = new NirFunction("memory", new([], [I32]), new(0), [new(new(0), [e],
        [
            new NirConstant(size, 4), new NirLocalAlloc(address, size, 4, new(e, e1)), new NirConstant(value, 0x12345678),
            new NirStore(address, value, NirByteOrder.Little, new(e1, e2)), new NirPure(addressBits, NirPureCode.AddressToBits, [address]),
            new NirPure(addressAgain, NirPureCode.BitsToAddress, [addressBits]), new NirLoad(loaded, addressAgain, NirByteOrder.Big, new(e2, e3))
        ], new NirReturn([loaded], e3))]);
        var module = new NirModule([function], [], [new("memory", 64, 0x1000, 0x1000)], []);
        Require(NirValidator.Validate(module).IsValid, "typed byte memory validates");
        var result = NirInterpreter.Execute(module, "memory", []);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 0x78563412, "address roundtrip aliases one byte store with explicit order");
        var context = new NirExecutionContext(module);
        Require(NirInterpreter.Execute(module, "memory", [], context).Status == NirExecutionStatus.Returned, "local allocation first call");
        Require(context.Memory.Read("memory", 0x1000, 4).Error == "UnmappedMemory", "local lifetime ends on return");
        Require(NirInterpreter.Execute(module, "memory", [], context).Status == NirExecutionStatus.Returned, "local interval reusable after return");
        var withoutStore = function with { Blocks = [function.Blocks[0] with
        {
            Operations = [new NirConstant(size, 4), new NirLocalAlloc(address, size, 4, new(e, e1)), new NirLoad(loaded, address, NirByteOrder.Little, new(e1, e3))]
        }] };
        var unknownModule = module with { Functions = [withoutStore] };
        Require(NirInterpreter.Execute(unknownModule, "memory", []).Status == NirExecutionStatus.MissingInput, "uninitialized memory is not zero");
        var tooLarge = module with { MemorySpaces = [new("memory", 64, 0x1000, 2)] };
        Require(NirInterpreter.Execute(tooLarge, "memory", []).Status == NirExecutionStatus.Faulted, "allocation failure is explicit");
        var staticAddress = new NirValue(new(20), address.Type); var observed = NirValue.Bits(21, 32); var se = NirValue.Effect(22);
        var observer = new NirFunction("observer", new([], [I32]), new(0), [new(new(0), [e],
            [new NirConstant(staticAddress, 0x200), new NirLoad(observed, staticAddress, NirByteOrder.Little, new(e, se))], new NirReturn([observed], se))]);
        var staticModule = module with { Functions = [observer], DataObjects = [new("data", "memory", 0x200, [1, 2, 3, 4], false)] };
        Require(NirInterpreter.Execute(staticModule, "observer", []).Values[0].Bits == 0x04030201, "module data independent of original image");
        var staticContext = new NirExecutionContext(staticModule);
        Require(staticContext.Memory.Write("memory", 0x200, [9]).Error == "WritePermissionFault", "read-only data rejects write");
        return 9;
    }

    private static int MemoryWrapping()
    {
        var module = new NirModule([], [], [new("wrapped", 8, 0, 0)], []);
        var memory = new NirMemory(module);
        Require(memory.Map(new("wrapped", 254, 2, true), [1, 2]) is null &&
            memory.Map(new("wrapped", 0, 2, true), [3, 4]) is null, "boundary bytes map as two non-wrapping intervals");
        Require(memory.Read("wrapped", 254, 4).Bytes.SequenceEqual(new byte[] { 1, 2, 3, 4 }), "byte read wraps at address width");
        Require(memory.Write("wrapped", 254, [5, 6, 7, 8]).Success, "byte write wraps at address width");
        Require(memory.Read("wrapped", 254, 4).Bytes.SequenceEqual(new byte[] { 5, 6, 7, 8 }), "wrapped write preserves byte order");
        Require(memory.Read("wrapped", -1, 1).Error == "AddressRangeFault" && memory.Write("wrapped", -1, [9]).Error == "AddressRangeFault",
            "negative access bases are rejected instead of wrapped");
        Require(memory.Read("wrapped", 256, 1).Error == "AddressRangeFault" && memory.Write("wrapped", 256, [9]).Error == "AddressRangeFault",
            "out-of-width access bases are rejected instead of wrapped");
        Require(memory.Read("wrapped", 256, 0).Error == "AddressRangeFault" && memory.Write("wrapped", 256, []).Error == "AddressRangeFault",
            "empty access still requires a valid base");
        Require(memory.Read("wrapped", 0, -1).Error == "AddressRangeFault", "negative read length is rejected");
        Require(memory.Read("wrapped", 254, 4).Bytes.SequenceEqual(new byte[] { 5, 6, 7, 8 }), "invalid bases do not modify mapped bytes");
        Require(memory.Map(new("wrapped", 254, 3, true), [5, 6, 7]) == "InvalidMemoryInput", "mapped intervals cannot wrap");
        Require(!NirValidator.Validate(module with { DataObjects = [new("crossing", "wrapped", 254, [1, 2, 3], false)] }).IsValid,
            "data object intervals cannot wrap");
        Require(!NirValidator.Validate(module with { MemorySpaces = [new("wrapped", 8, 254, 3)] }).IsValid,
            "local arena intervals cannot wrap");
        var local = new NirMemory(module with { MemorySpaces = [new("wrapped", 8, 254, 2)] });
        Require(local.Allocate("wrapped", 3, 1) is null && local.Allocate("wrapped", 2, 1) is { Address: var allocated } && allocated == 254 &&
            local.Allocate("wrapped", 1, 1) is null, "local allocations stay inside the non-wrapping arena");

        var unmapped = new NirMemory(module);
        Require(unmapped.Map(new("wrapped", 254, 2, true), [1, 2]) is null && unmapped.Read("wrapped", 254, 4).Error == "UnmappedMemory",
            "wrapped read checks the low-address mapping");
        Require(unmapped.Write("wrapped", 254, [5, 6, 7, 8]).Error == "UnmappedMemory" &&
            unmapped.Read("wrapped", 254, 2).Bytes.SequenceEqual(new byte[] { 1, 2 }), "unmapped wrapped write does not partially commit");
        var readOnly = new NirMemory(module with
        {
            DataObjects = [new("high", "wrapped", 254, [1, 2], true), new("low", "wrapped", 0, [3, 4], false)]
        });
        Require(readOnly.Read("wrapped", 254, 4).Bytes.SequenceEqual(new byte[] { 1, 2, 3, 4 }), "wrapped read permits read-only bytes");
        Require(readOnly.Write("wrapped", 254, [5, 6, 7, 8]).Error == "WritePermissionFault" &&
            readOnly.Read("wrapped", 254, 4).Bytes.SequenceEqual(new byte[] { 1, 2, 3, 4 }), "denied wrapped write leaves both intervals unchanged");
        var uninitialized = new NirMemory(module);
        Require(uninitialized.Map(new("wrapped", 254, 2, true), [1, 2]) is null && uninitialized.Map(new("wrapped", 0, 2, true)) is null,
            "wrapped input can explicitly leave bytes uninitialized");
        var missing = uninitialized.Read("wrapped", 254, 4);
        Require(missing is { Error: "UninitializedMemory", MissingInput: true, Bytes.IsEmpty: true }, "wrapped uninitialized read requires input without a partial result");

        var repeated = new NirMemory(module);
        Require(repeated.Map(new("wrapped", 0, 256, true), [.. Enumerable.Range(0, 256).Select(index => (byte)index)]) is null,
            "the full address space is one valid interval");
        Require(repeated.Read("wrapped", 254, 260).Bytes.SequenceEqual(Enumerable.Range(0, 260).Select(index => (byte)((254 + index) & 255))),
            "reads longer than the address space revisit bytes in order");
        Require(repeated.Write("wrapped", 254, [.. Enumerable.Range(0, 260).Select(index => (byte)(index < 256 ? 1 : 2))]).Success &&
            repeated.Read("wrapped", 0, 256).Bytes.SequenceEqual(Enumerable.Range(0, 256).Select(index => (byte)(index < 2 || index >= 254 ? 2 : 1))),
            "repeated write addresses retain the last byte assigned");
        return 22;
    }

    private static int Validation()
    {
        var valid = AddFunction();
        var block = valid.Blocks[0];
        var a = block.Parameters[0]; var b = block.Parameters[1]; var e = block.Parameters[2];
        var r = ((NirPure)block.Operations[0]).Result;
        Require(!NirValidator.Validate(Module(valid with { Blocks = [block with { Parameters = [a, a, e] }] })).IsValid, "duplicate SSA definitions rejected");
        Require(!NirValidator.Validate(Module(valid with { Blocks = [block with { Operations = [new NirPure(r, NirPureCode.Add, [r, b])] }] })).IsValid, "self use rejected");
        Require(!NirValidator.Validate(Module(valid with { Blocks = [block with { Terminator = new NirReturn([NirValue.Bits(55, 32)], e) }] })).IsValid, "undefined use rejected");
        var chosen = NirValue.Bits(4, 32); var e1 = NirValue.Effect(5);
        var choice = valid with { Blocks = [block with { Operations = [.. block.Operations, new NirChoose(chosen, new(e, e1))], Terminator = new NirReturn([r], e1) }] };
        var choiceModule = Module(choice);
        Require(NirInterpreter.Execute(choiceModule, "add", [NirRuntimeValue.Integer(32, 1), NirRuntimeValue.Integer(32, 2)]).Status == NirExecutionStatus.MissingInput, "choice requires an input");
        var context = new NirExecutionContext(choiceModule); context.Choices.Enqueue(42);
        Require(NirInterpreter.Execute(choiceModule, "add", [NirRuntimeValue.Integer(32, 1), NirRuntimeValue.Integer(32, 2)], context).Status == NirExecutionStatus.Returned, "explicit choice executes");
        Require(!NirValidator.Validate(Module(choice with { Blocks = [choice.Blocks[0] with { Terminator = new NirReturn([r], e) }] })).IsValid, "stale return Effect rejected");
        Require(NirInterpreter.Execute(Module(valid), "add", [NirRuntimeValue.Integer(32, -1), NirRuntimeValue.Integer(32, 1)]).Status == NirExecutionStatus.InvalidInput, "negative raw bit input rejected");
        var leftEffect = NirValue.Effect(10); var rightEffect = NirValue.Effect(11); var mergeEffect = NirValue.Effect(12);
        var predicate = NirValue.Bits(13, 1); var leftOnly = NirValue.Bits(14, 32);
        var diamond = valid with
        {
            Blocks =
            [
                new(new(0), [a, b, e], [new NirPure(predicate, NirPureCode.Ult, [a, b])], new NirBranch(predicate, new(new(1), [e]), new(new(2), [e]))),
                new(new(1), [leftEffect], [new NirPure(leftOnly, NirPureCode.Add, [a, b])], new NirJump(new(new(3), [leftEffect]))),
                new(new(2), [rightEffect], [], new NirJump(new(new(3), [rightEffect]))),
                new(new(3), [mergeEffect], [], new NirReturn([leftOnly], mergeEffect))
            ]
        };
        Require(NirValidator.Validate(Module(diamond)).Diagnostics.Any(d => d.Code == "ssa-dominance"), "branch-local definition cannot escape without a merge parameter");
        Require(NirValidator.Validate(Module(valid with { Blocks = [block with { Operations = [new NirPure(r, NirPureCode.Add, default)] }] })).Diagnostics.Any(d => d.Code == "operation-array"),
            "malformed operand arrays return structured validation errors");
        return 9;
    }
}
