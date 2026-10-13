using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Arm64;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;
using Cpp2CS.X64;
using Iced.Intel;

namespace Cpp2CS.Validation;

public static class NirRecoveryChecks
{
    internal const ulong Entry = 0x1000;
    internal const ulong Callee = 0x1100;
    internal const ulong ReturnSentinel = 0x7FFF0000;
    internal const ulong Stack = 0x70001008;

    public static int Run()
    {
        var checks = 0;
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var caller = Caller(architecture);
            var callerContracts = new[] { Contract(architecture, "caller", Entry, 2), Contract(architecture, "add", Callee, 2) };
            var recoveredCaller = Recover(caller, callerContracts);
            CoreChecks.Require(recoveredCaller.Complete, Explain(recoveredCaller));
            var function = recoveredCaller.Module.Functions.Single(f => f.Id == "caller");
            CoreChecks.Require(function.Blocks.SelectMany(b => b.Operations).Count(op => op is NirCall) == 1,
                "recovered caller contains one logical call, independent of machine call preparation");
            CoreChecks.Require(function.Blocks.SelectMany(b => b.Operations).All(op => op is not (NirLoad or NirStore)),
                "proven private spill and call protocol do not survive as NIR memory operations");
            checks += 3;
            BigInteger[] cases = [0, 1, 31, uint.MaxValue, BigInteger.One << 63, ulong.MaxValue];
            foreach (var a in cases)
            foreach (var b in cases)
                checks += Compare(caller, recoveredCaller.Module, "caller", Entry, [a, b],
                    (a * 2 + b + 1) & MirInterpreter.Mask(64));

            var indirectCaller = IndirectCaller(architecture);
            var indirectSite = architecture == Architecture.Arm64 ? 0x100CUL : 0x1010UL;
            var boundIndirect = Recover(indirectCaller, callerContracts, new(IndirectCallTargets:
                ImmutableDictionary<ulong, ulong>.Empty.Add(indirectSite, Callee)));
            CoreChecks.Require(boundIndirect.Complete, Explain(boundIndirect));
            CoreChecks.Require(boundIndirect.Functions.Single(f => f.Graph.Contract.Name == "caller").Graph.Dependencies
                .Contains($"adopted-call-target:0x{indirectSite:X}:0x{Callee:X}"), "indirect target conversion retains its adopted evidence outside NIR");
            checks += 2 + Compare(indirectCaller, boundIndirect.Module, "caller", Entry, [7, 11], 26);

            var branch = Branch(architecture);
            var recoveredBranch = Recover(branch, [Contract(architecture, "maximum", Entry, 2)]);
            CoreChecks.Require(recoveredBranch.Complete, Explain(recoveredBranch));
            checks++;
            foreach (var a in cases)
            foreach (var b in cases)
                checks += Compare(branch, recoveredBranch.Module, "maximum", Entry, [a, b], BigInteger.Max(a, b));

            var joinedLocal = JoinedLocal(architecture);
            var recoveredLocal = Recover(joinedLocal, [Contract(architecture, "joined_local", Entry, 1)]);
            CoreChecks.Require(recoveredLocal.Complete, Explain(recoveredLocal));
            CoreChecks.Require(recoveredLocal.Module.Functions.Single().Blocks.SelectMany(block => block.Operations)
                .Any(operation => operation is NirLocalAlloc), "different incoming stores retain an initialized logical local object");
            checks += 2;
            foreach (var value in new BigInteger[] { 0, 1, ulong.MaxValue })
                checks += Compare(joinedLocal, recoveredLocal.Module, "joined_local", Entry, [value], value.IsZero ? 22 : 11);
            var partialLocal = Recover(JoinedLocal(architecture, false), [Contract(architecture, "partial_local", Entry, 1)]);
            CoreChecks.Require(!partialLocal.Complete, "a local initialized on only one branch cannot acquire a fabricated value at the join");
            checks++;

            var loop = Loop(architecture);
            var recoveredLoop = Recover(loop,
                [Contract(architecture, "loop", Entry, 1), Contract(architecture, "add", Callee, 2)]);
            CoreChecks.Require(recoveredLoop.Complete, Explain(recoveredLoop));
            CoreChecks.Require(recoveredLoop.Module.Functions.Single(f => f.Id == "loop").Blocks
                .Any(block => block.Id != recoveredLoop.Module.Functions.Single(f => f.Id == "loop").Entry &&
                    block.Parameters.Any(value => value.Type is NirBitsType)), "loop carries ordinary SSA values through block parameters");
            checks += 2;
            foreach (var count in new[] { 0, 1, 2, 3, 7, 19 })
                checks += Compare(loop, recoveredLoop.Module, "loop", Entry, [new BigInteger(count)], count);

            var recursive = Recursive(architecture);
            var recoveredRecursive = Recover(recursive, [Contract(architecture, "recursive", Entry, 1)]);
            CoreChecks.Require(recoveredRecursive.Complete, Explain(recoveredRecursive));
            checks++;
            foreach (var count in new[] { 0, 1, 2, 3, 7 })
                checks += Compare(recursive, recoveredRecursive.Module, "recursive", Entry, [new BigInteger(count)], count);

            foreach (var arity in new[] { 5, 9 })
            {
                var stackArguments = StackArguments(architecture, arity);
                var recoveredArguments = Recover(stackArguments, [Contract(architecture, "stack_arguments", Entry, arity)]);
                CoreChecks.Require(recoveredArguments.Complete, Explain(recoveredArguments));
                var values = Enumerable.Range(1, arity).Select(value => new BigInteger(value)).ToArray();
                checks += 1 + Compare(stackArguments, recoveredArguments.Module, "stack_arguments", Entry, values, arity + 1);
            }
            var argumentJoin = IncomingStackArgumentJoin(architecture);
            var incomingArity = architecture == Architecture.Arm64 ? 9 : 5;
            var recoveredArgumentJoin = Recover(argumentJoin, [Contract(architecture, "argument_join", Entry, incomingArity)]);
            CoreChecks.Require(recoveredArgumentJoin.Complete, Explain(recoveredArgumentJoin));
            checks++;
            foreach (var condition in new[] { 0, 1 })
            {
                var values = Enumerable.Range(100, incomingArity).Select(value => new BigInteger(value)).ToArray();
                values[0] = condition;
                checks += Compare(argumentJoin, recoveredArgumentJoin.Module, "argument_join", Entry, values,
                    condition == 0 ? values[^1] : 42);
            }

            var missing = Recover(caller, [callerContracts[0]]);
            CoreChecks.Require(!missing.Complete && missing.Module.Functions.All(f => f.Id != "caller"),
                "unknown callee signature remains a recovery gap, never an opaque NIR call");
            CoreChecks.Require(missing.Functions.Single().Graph.Gaps.Any(gap => gap.Kind == RecoveryGapKind.MissingCallContract),
                "unknown callee reports the missing interface contract");
            checks += 2;

            var contradicted = Recover(caller,
                [callerContracts[0], Contract(architecture, "bad_stop", Callee, 2, returns: false)]);
            CoreChecks.Require(contradicted.Functions.All(function => !function.Complete) &&
                contradicted.Module.Externals.All(external => external.Id != "bad_stop"),
                "a known no-return callee with RET contradicts its contract and invalidates its caller instead of becoming external");
            checks++;

            var deadFloat = new FixtureSource(architecture, "fixture:nir-dead-float-environment");
            deadFloat.Add(Entry, architecture == Architecture.Arm64 ? ["0228611E", "E00080D2", "C0035FD6"]
                : ["F20F58C1", "B807000000", "C3"]);
            var unrecoveredEnvironment = Recover(deadFloat, [Contract(architecture, "dead_float", Entry, 0)]);
            CoreChecks.Require(!unrecoveredEnvironment.Complete && unrecoveredEnvironment.Gaps
                .Any(gap => gap.Code == "contract.unmodeled-environment"),
                "dead floating result does not erase observable FPSR or MXCSR writes: " + Explain(unrecoveredEnvironment));
            checks++;

            var noReturn = Contract(architecture, "stop", Callee, 1, returns: false);
            var stoppedGraph = FunctionGraphBuilder.Build(caller, callerContracts[0], [callerContracts[0], noReturn]);
            var stoppedCall = stoppedGraph.Blocks.SelectMany(block => block.Edges).Single(edge => edge.Kind == DerivedEdgeKind.Call);
            CoreChecks.Require(stoppedCall.Continuation is null && stoppedCall.TargetBlock is null &&
                stoppedCall.Call!.Interface.Arguments.Length == 1,
                "no-return call has no fabricated continuation and retains its logical input");
            checks++;
            checks += NoReturn(architecture);
            checks += VisibleMemory(architecture);

            var indirect = new FixtureSource(architecture, "fixture:nir-unknown-indirect-call");
            indirect.Add(Entry, architecture == Architecture.Arm64 ? "00023FD6" : "FFD0");
            var indirectResult = Recover(indirect, [Contract(architecture, "indirect", Entry, 1)]);
            CoreChecks.Require(!indirectResult.Complete && indirectResult.Functions.Single().Graph.Gaps
                .Any(gap => gap.Kind == RecoveryGapKind.UnknownCallTarget),
                "unbound indirect call remains a gap, never a zero-argument call");
            checks++;

            var malformed = new FixtureSource(architecture, "fixture:nir-wrong-return-protocol");
            if (architecture == Architecture.Arm64) malformed.Add(Entry, "1E0080D2", "C0035FD6");
            else malformed.Add(Entry, "4883EC08", "C3");
            var invalidProtocol = Recover(malformed, [Contract(architecture, "broken", Entry, 1)]);
            CoreChecks.Require(!invalidProtocol.Complete && invalidProtocol.Module.Functions.IsEmpty,
                "wrong return target or stack protocol cannot produce a complete NIR function");
            checks++;

            var escape = EscapedFrame(architecture);
            var mutator = new FunctionContract("mutate", Callee,
                new([new(64, RecoveryScalarKind.Address)], null),
                architecture == Architecture.Arm64 ? MachineAbiKind.Aapcs64 : MachineAbiKind.WindowsX64,
                new(false, true, false, false, true, false, false),
                ["explicit fixture mutates its address argument"], new(true, true, true, true));
            var escaped = Recover(escape, [Contract(architecture, "escaped_frame", Entry, 1), mutator]);
            var escapedCaller = escaped.Functions.Single(function => function.Graph.Contract.Name == "escaped_frame");
            CoreChecks.Require(!escapedCaller.Complete && !escapedCaller.Diagnostics.IsEmpty &&
                escaped.Module.Functions.All(function => function.Id != "escaped_frame"),
                "frame address escape is an explicit first-stage gap, never stale spill forwarding");
            var escapedMachine = ExecuteMachine(escape, Entry, InitialState(architecture, [new BigInteger(99)], escape.Addresses));
            CoreChecks.Require(escapedMachine.Result == 42, "actual escaped-frame call overwrites the saved value");
            checks += 2;
        }
        return checks;
    }

    internal static NirRecoveryResult Recover(IRegionInstructionSource source, IEnumerable<FunctionContract> contracts,
        FunctionGraphOptions? graphOptions = null)
    {
        var recovered = NirRecovery.Recover(source, contracts,
            new(AssumeNormalExecution: true, AssumePrivateValidFrames: true, GraphOptions: graphOptions));
        var serialized = NirJson.Serialize(recovered.Module);
        CoreChecks.Require(!serialized.Contains("\"architecture\"", StringComparison.OrdinalIgnoreCase) &&
            !serialized.Contains("\"abi\"", StringComparison.OrdinalIgnoreCase) &&
            !serialized.Contains("\"stateMap\"", StringComparison.OrdinalIgnoreCase), "NIR serialization contains no machine execution configuration");
        var detached = NirJson.Deserialize(serialized);
        CoreChecks.Require(NirValidator.Validate(detached).IsValid, "detached and deserialized NIR remains independently valid");
        return recovered with { Module = detached };
    }

    internal static string Explain(NirRecoveryResult result) => string.Join("; ", result.Functions.SelectMany(f => f.Diagnostics)
        .Select(d => $"0x{d.Address:X} {d.Code}: {d.Message}"));

    internal static int Compare(FixtureSource source, NirModule module, string function, ulong entry,
        BigInteger[] arguments, BigInteger expected)
    {
        var state = InitialState(source.Architecture, arguments, source.Addresses);
        var machine = ExecuteMachine(source, entry, state);
        var input = arguments.Select(value => NirRuntimeValue.Integer(64, value)).ToImmutableArray();
        var nir = NirInterpreter.Execute(module, function, input);
        CoreChecks.Require(nir.Status == NirExecutionStatus.Returned,
            $"NIR fixture execution: {source.Architecture} {function}: {nir.Status} {nir.Detail}");
        CoreChecks.Require(nir.Values.Length == 1 && nir.Values[0].Bits == machine.Result && machine.Result == expected,
            $"NIR/MIR/independent arithmetic fixture result: {source.Architecture} {function}");
        var stack = source.Architecture == Architecture.Arm64 ? "sp" : "rsp";
        CoreChecks.Require(state.Slots[stack] == (source.Architecture == Architecture.Arm64 ? Stack - 8 : Stack + 8),
            "complete machine execution balances its own call and return protocol");
        string[] preserved = source.Architecture == Architecture.Arm64 ? ["x19", "x20", "x29"] : ["rbx", "rsi", "rdi"];
        foreach (var slot in preserved)
            CoreChecks.Require(state.Slots[slot] == new BigInteger(0xA55AA55A12345678UL), "machine fixture restores nonvolatile state");
        return 3 + preserved.Length;
    }

    internal static FunctionContract Contract(Architecture architecture, string name, ulong address,
        int arguments, int width = 64, bool returns = true) => new(name, address,
        new(Enumerable.Repeat(new RecoveryScalarType(width), arguments).ToImmutableArray(),
            returns ? new RecoveryScalarType(width) : null),
        architecture == Architecture.Arm64 ? MachineAbiKind.Aapcs64 : MachineAbiKind.WindowsX64,
        new(false, false, false, false, returns, false, !returns),
        ["handwritten scalar fixture interface; no managed-language inference"], new(true, true, true, true));

    // 所有片段均来自真实机器编码；机器侧直接执行被调体和 RET，不调用恢复摘要。
    internal static FixtureSource Caller(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-caller");
        if (architecture == Architecture.Arm64)
        {
            source.Add(Entry, "FD7BBEA9", "E00B00F9", ArmCall(0x1008, Callee),
                "E10B40F9", "0000018B", "00040091", "FD7BC2A8", "C0035FD6");
            source.Add(Callee, "0000018B", "C0035FD6");
        }
        else
        {
            source.Add(Entry, "4883EC38", "48894C2420", X64Call(0x1009, Callee),
                "4803442420", "4883C001", "4883C438", "C3");
            source.Add(Callee, "488D0411", "C3");
        }
        return source;
    }

    internal static FixtureSource Branch(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-branch");
        if (architecture == Architecture.Arm64)
            source.Add(Entry, "1F0001EB", "42000054", "E00301AA", "C0035FD6");
        else
            source.Add(Entry, "4839D1", "7303", "4889D1", "4889C8", "C3");
        return source;
    }

    private static FixtureSource JoinedLocal(Architecture architecture, bool initializedOnBothBranches = true)
    {
        var source = new FixtureSource(architecture, "fixture:nir-local-join");
        if (architecture == Architecture.Arm64)
            source.Add(Entry, "FF4300D1", "800000B4", "610180D2", "E10300F9", "03000014",
                "C10280D2", initializedOnBothBranches ? "E10300F9" : "1F2003D5", "E00340F9", "FF430091", "C0035FD6");
        else
            source.Add(Entry, "4883EC18", "4885C9", "740B", "48C74424080B000000", "EB09",
                initializedOnBothBranches ? "48C744240816000000" : "660F1F840000000000", "488B442408", "4883C418", "C3");
        return source;
    }

    private static FixtureSource IndirectCaller(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-bound-indirect-call");
        if (architecture == Architecture.Arm64)
        {
            source.Add(Entry, "FD7BBEA9", "E00B00F9", "102082D2", "00023FD6",
                "E10B40F9", "0000018B", "00040091", "FD7BC2A8", "C0035FD6");
            source.Add(Callee, "0000018B", "C0035FD6");
        }
        else
        {
            source.Add(Entry, "4883EC38", "48894C2420", "48C7C000110000", "FFD0",
                "4803442420", "4883C001", "4883C438", "C3");
            source.Add(Callee, "488D0411", "C3");
        }
        return source;
    }

    private static int NoReturn(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-noreturn");
        if (architecture == Architecture.Arm64) source.Add(Entry, ArmCall(Entry, Callee));
        else source.Add(Entry, "4883EC28", X64Call(Entry + 4, Callee));
        var result = Recover(source, [Contract(architecture, "fatal_caller", Entry, 1, returns: false),
            Contract(architecture, "stop", Callee, 1, returns: false)]);
        var caller = result.Functions.Single(f => f.Graph.Contract.Name == "fatal_caller");
        CoreChecks.Require(caller.Complete && caller.Function!.Blocks.Any(block => block.Terminator is NirNoReturnCall),
            "no-return call emits a logical terminal call without a continuation");
        var context = new NirExecutionContext(result.Module);
        var invoked = false;
        context.Externals["stop"] = invocation =>
        {
            CoreChecks.Require(invocation.Arguments.Length == 1 && invocation.Arguments[0].Bits == 123,
                "no-return external still receives its declared input");
            invoked = true;
            return new(NirExternalOutcome.Terminate, [], "fixture termination");
        };
        var execution = NirInterpreter.Execute(result.Module, "fatal_caller", [NirRuntimeValue.Integer(64, 123)], context);
        CoreChecks.Require(invoked && execution.Status == NirExecutionStatus.Terminated, "no-return execution does not fabricate a return result");
        var misaligned = new FixtureSource(architecture, "fixture:nir-misaligned-noreturn-call");
        if (architecture == Architecture.Arm64) misaligned.Add(Entry, "FF2300D1", ArmCall(Entry + 4, Callee));
        else misaligned.Add(Entry, X64Call(Entry, Callee));
        var rejected = Recover(misaligned, [Contract(architecture, "misaligned", Entry, 1, returns: false),
            Contract(architecture, "stop", Callee, 1, returns: false)]);
        CoreChecks.Require(!rejected.Functions.Single(function => function.Graph.Contract.Name == "misaligned").Complete,
            "an explicit stack-alignment contradiction is not authorized by a normal-path domain");
        return 4;
    }

    private static int VisibleMemory(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-visible-memory");
        source.Add(Entry, architecture == Architecture.Arm64 ? ["010000F9", "000040F9", "C0035FD6"]
            : ["488911", "488B01", "C3"]);
        var contract = Contract(architecture, "write_read", Entry, 2) with
        {
            Signature = new([new(64, RecoveryScalarKind.Address), new(64)], new(64)),
            Effects = new(true, true, false, false, true, false, false)
        };
        var recovered = Recover(source, [contract]);
        CoreChecks.Require(recovered.Complete, Explain(recovered));
        var operations = recovered.Module.Functions.Single().Blocks.SelectMany(block => block.Operations).ToArray();
        CoreChecks.Require(operations.Any(operation => operation is NirLoad) && operations.Any(operation => operation is NirStore),
            "ordinary visible memory retains ordered load and store effects");
        var noSequential = Recover(source, [contract with { Domain = new(true, true, true, false) }]);
        CoreChecks.Require(!noSequential.Complete, "normal execution alone cannot assume sequential program memory");
        var checks = 3;
        var space = recovered.Module.MemorySpaces.Single().Id;
        foreach (var address in new[] { 0x500000UL, ulong.MaxValue - 3 })
        foreach (var value in new BigInteger[] { 0, 17, BigInteger.One << 63, ulong.MaxValue })
        {
            var state = InitialState(architecture, [new BigInteger(address), value], source.Addresses);
            for (var i = 0; i < 8; i++) state.Memory[unchecked(address + (ulong)i)] = 0xA5;
            var machine = ExecuteMachine(source, Entry, state);
            var context = new NirExecutionContext(recovered.Module);
            var firstLength = address == ulong.MaxValue - 3 ? 4 : 8;
            CoreChecks.Require(context.Memory.Map(new(space, address, firstLength, true),
                [.. Enumerable.Repeat((byte)0xA5, firstLength)]) is null,
                "visible memory fixture maps the same initial bytes");
            if (firstLength == 4)
            {
                // 核对两层的模地址合同，不证明该地址可被实际硬件访问。
                CoreChecks.Require(context.Memory.Map(new(space, 0, 4, true), [0xA5, 0xA5, 0xA5, 0xA5]) is null,
                    "wrapped visible memory maps its low-address bytes separately");
                checks++;
            }
            var execution = NirInterpreter.Execute(recovered.Module, "write_read",
                [NirRuntimeValue.Address(space, 64, address), NirRuntimeValue.Integer(64, value)], context);
            CoreChecks.Require(execution.Status == NirExecutionStatus.Returned && execution.Values.Single().Bits == value && machine.Result == value,
                "visible load/store result agrees across real machine instructions and detached NIR");
            CoreChecks.Require(context.Memory.Read(space, address, 8).Bytes.SequenceEqual(
                Enumerable.Range(0, 8).Select(i => state.Memory[unchecked(address + (ulong)i)])), "visible memory bytes agree after execution");
            checks += 3;
        }
        return checks;
    }

    internal static FixtureSource Loop(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-loop-call");
        if (architecture == Architecture.Arm64)
        {
            source.Add(Entry, "FD7BBEA9", "F35301A9", "F30300AA", "F4031FAA",
                "F30000B4", "E00314AA", "210080D2", ArmCall(0x101C, Callee),
                "F40300AA", "730600D1", "FAFFFF17", "E00314AA", "F35341A9", "FD7BC2A8", "C0035FD6");
            source.Add(Callee, "0000018B", "C0035FD6");
        }
        else
        {
            source.Add(Entry, "53", "56", "4883EC28", "4889CB", "31F6", "4885DB", "7415",
                "4889F1", "BA01000000", X64Call(0x1018, Callee), "4889C6", "48FFCB", "EBE6",
                "4889F0", "4883C428", "5E", "5B", "C3");
            source.Add(Callee, "488D0411", "C3");
        }
        return source;
    }

    internal static FixtureSource Recursive(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-recursive-call");
        if (architecture == Architecture.Arm64)
            source.Add(Entry, "FD7BBFA9", "800000B4", "000400D1", ArmCall(0x100C, Entry),
                "00040091", "FD7BC1A8", "C0035FD6");
        else
            source.Add(Entry, "4883EC28", "4885C9", "740D", "48FFC9", X64Call(0x100C, Entry),
                "48FFC0", "EB02", "31C0", "4883C428", "C3");
        return source;
    }

    internal static FixtureSource StackArguments(Architecture architecture, int arity)
    {
        var source = new FixtureSource(architecture, "fixture:nir-stack-arguments");
        if (architecture == Architecture.Arm64)
        {
            if (arity == 5) source.Add(Entry, "0000048B", "C0035FD6");
            else source.Add(Entry, "E80340F9", "0000088B", "C0035FD6");
        }
        else source.Add(Entry, arity == 5 ? "488B442428" : "488B442448", "4801C8", "C3");
        return source;
    }

    private static FixtureSource IncomingStackArgumentJoin(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-incoming-stack-argument-join");
        if (architecture == Architecture.Arm64)
            source.Add(Entry, "600000B4", "410580D2", "E10300F9", "E00340F9", "C0035FD6");
        else
            source.Add(Entry, "4885C9", "7409", "48C74424282A000000", "488B442428", "C3");
        return source;
    }

    internal static FixtureSource EscapedFrame(Architecture architecture)
    {
        var source = new FixtureSource(architecture, "fixture:nir-frame-escape");
        if (architecture == Architecture.Arm64)
        {
            source.Add(Entry, "FD7BBEA9", "E00B00F9", "E0430091", ArmCall(0x100C, Callee),
                "E00B40F9", "FD7BC2A8", "C0035FD6");
            source.Add(Callee, "410580D2", "010000F9", "C0035FD6");
        }
        else
        {
            source.Add(Entry, "4883EC38", "48894C2420", "488D4C2420", X64Call(0x100E, Callee),
                "488B442420", "4883C438", "C3");
            source.Add(Callee, "48C7012A000000", "C3");
        }
        return source;
    }

    internal static MachineState InitialState(Architecture architecture, IReadOnlyList<BigInteger> arguments,
        IEnumerable<ulong> instructionAddresses)
    {
        var state = NativeExecutionChecks.State(architecture);
        foreach (var (slot, width) in StateLayout.For(architecture))
            state.Slots[slot] = new BigInteger(0xA55AA55A12345678UL) & MirInterpreter.Mask(width);
        state.Slots[architecture == Architecture.Arm64 ? "fpcr" : "mxcsr"] = architecture == Architecture.Arm64 ? 0 : 0x1F80;
        var stack = architecture == Architecture.Arm64 ? Stack - 8 : Stack;
        state.Slots[architecture == Architecture.Arm64 ? "sp" : "rsp"] = stack;
        if (architecture == Architecture.Arm64)
        {
            state.Slots["x30"] = ReturnSentinel;
            state.Slots["btype"] = 0;
            state.Slots["bti_bt0"] = 0;
        }
        else state.Slots["df"] = 0;
        for (var index = -1024; index < 128; index++) state.Memory[unchecked(stack + (ulong)index)] = (byte)index;
        if (architecture == Architecture.X64)
            for (var index = 0; index < 8; index++) state.Memory[stack + (ulong)index] = (byte)(ReturnSentinel >> (8 * index));
        string[] registers = architecture == Architecture.Arm64
            ? ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"] : ["rcx", "rdx", "r8", "r9"];
        for (var index = 0; index < arguments.Count; index++)
        {
            if (index < registers.Length) state.Slots[registers[index]] = arguments[index];
            else
            {
                var argumentAddress = stack + (architecture == Architecture.Arm64 ? 0UL : 40UL) + 8UL * (ulong)(index - registers.Length);
                for (var offset = 0; offset < 8; offset++) state.Memory[argumentAddress + (ulong)offset] = (byte)((arguments[index] >> (8 * offset)) & 255);
            }
        }
        foreach (var address in instructionAddresses) state.CodeGuardedPages[address >> 12] = false;
        return state;
    }

    internal static (BigInteger Result, MachineState State, int Instructions) ExecuteMachine(
        IRegionInstructionSource source, ulong entry, MachineState state, int budget = 4096)
    {
        var address = entry;
        var count = 0;
        while (address != ReturnSentinel && count < budget)
        {
            var decoded = source.Decode(address);
            CoreChecks.Require(decoded.Instruction is not null, $"machine fixture decode at 0x{address:X}: {decoded.Reason}");
            var result = MirInterpreter.Execute(decoded.Instruction!, state);
            CoreChecks.Require(result.Stop is null && result.NextAddress is not null,
                $"machine fixture stops at 0x{address:X}: {result.Stop?.Reason}");
            address = result.NextAddress!.Value;
            count++;
        }
        CoreChecks.Require(address == ReturnSentinel, "machine fixture must execute the complete call/return protocol within budget");
        return (state.Slots[source.Architecture == Architecture.Arm64 ? "x0" : "rax"], state, count);
    }

    internal static string ArmCall(ulong address, ulong target)
    {
        var bytes = new byte[4];
        BinaryPrimitives.WriteUInt32LittleEndian(bytes, 0x94000000U | ((uint)((long)target - (long)address) >> 2 & 0x03FFFFFF));
        return Convert.ToHexString(bytes);
    }

    internal static string X64Call(ulong address, ulong target)
    {
        var bytes = new byte[5];
        bytes[0] = 0xE8;
        BinaryPrimitives.WriteInt32LittleEndian(bytes.AsSpan(1), checked((int)((long)target - (long)address - 5)));
        return Convert.ToHexString(bytes);
    }

    internal sealed class FixtureSource(Architecture architecture, string imageId) : IRegionInstructionSource
    {
        private readonly Dictionary<ulong, MirInstruction> instructions = [];
        public string ImageId => imageId;
        public Architecture Architecture => architecture;
        public IEnumerable<ulong> Addresses => instructions.Keys;
        public IEnumerable<MirInstruction> Instructions => instructions.Values;
        public void Add(ulong address, params string[] encodings)
        {
            foreach (var hex in encodings)
            {
                var bytes = Convert.FromHexString(hex);
                var origin = new InstructionOrigin(ImageId, address, (long)address, bytes);
                LiftResult lifted;
                if (Architecture == Architecture.Arm64) lifted = Arm64Lifter.Lift(origin);
                else
                {
                    var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes));
                    decoder.IP = address;
                    var decoded = decoder.Decode();
                    CoreChecks.Require(decoded.Length == bytes.Length, "fixture encoding must contain exactly one x64 instruction");
                    lifted = X64Lifter.Lift(origin, decoded);
                }
                CoreChecks.Require(lifted.Ir is not null, $"NIR machine fixture must lift: {hex}: {lifted.Reason}");
                instructions.Add(address, lifted.Ir!);
                address += (ulong)bytes.Length;
            }
        }
        public InstructionDecodeResult Decode(ulong address) => instructions.TryGetValue(address, out var instruction)
            ? InstructionDecodeResult.Supported(instruction)
            : InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unmapped, "NIR fixture has no instruction at this address");
    }
}
