using System.Collections.Immutable;
using System.Numerics;
using System.Text.Json;
using Cpp2CS.Arm64;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.X64;
using Iced.Intel;

namespace Cpp2CS.Validation;

public static class NativeExecutionChecks
{
    private const string ImageId = "fixture:native-execution";
    public static int Run()
    {
        var checks = 0;
        var loop = Builder(Architecture.Arm64, 0x1000);
        var next = loop.Sub(loop.Read("x9", 64), loop.Const(64, 1));
        loop.Write("x9", next);
        loop.Write("sp", loop.Add(loop.Read("sp", 64), loop.Const(64, 16)));
        loop.Write("x29", loop.Add(loop.Read("x29", 64), loop.Const(64, 3)));
        loop.Write("x30", loop.Add(loop.Read("x30", 64), loop.Const(64, 4)));
        var choice = loop.Undefined(8, "loop choice");
        loop.Write("x2", loop.Zext(loop.Add(choice, choice), 64));
        loop.Write("z", loop.Eq(next, loop.Const(64, 0)));
        var loopIr = loop.Finish(MirExit.Branch(loop.Read("z", 1), loop.Const(64, 0x1004), loop.Const(64, 0x1000)));
        var exit = Builder(Architecture.Arm64, 0x1004);
        exit.Write("x0", exit.Read("x29", 64));
        var graph = Graph(Architecture.Arm64, [loopIr, exit.Finish(MirExit.Next(0x1008))], [0x1000, 0x1004]);
        for (var iterations = 0; iterations <= 7; iterations++)
        {
            var state = State(Architecture.Arm64);
            state.Slots["x9"] = iterations;
            foreach (var value in Enumerable.Range(1, 16)) state.ChoiceInputs.Enqueue(value);
            checks += Compare(graph, 0x1000, state, 9);
        }
        checks += Compare(graph, 0x1004, State(Architecture.Arm64), 3);

        var parallel = Builder(Architecture.Arm64, 0x1000);
        graph = Graph(Architecture.Arm64,
            [parallel.Finish(MirExit.Branch(parallel.Read("z", 1), parallel.Const(64, 0x1004), parallel.Const(64, 0x1004)))], [0x1000]);
        var edgeIds = new HashSet<EdgeId>();
        foreach (var z in new[] { 0, 1 })
        {
            var state = State(Architecture.Arm64);
            state.Slots["z"] = z;
            checks += Compare(graph, 0x1000, state, 3);
            edgeIds.Add(NativeExecutor.Execute(StateSsaConverter.Convert(graph), 0x1000, Clone(state), 3).TraversedEdges[0]);
        }
        CoreChecks.Require(edgeIds.Count == 2, "parallel branch edges retain different dynamic identities");
        checks++;

        // 两个入口进入同一环的不同节点，不依赖唯一循环头或单一支配入口。
        var a = Builder(Architecture.Arm64, 0x2000);
        a.Write("x0", a.Add(a.Read("x0", 64), a.Const(64, 1)));
        var b = Builder(Architecture.Arm64, 0x2004);
        b.Write("x1", b.Xor(b.Read("x1", 64), b.Read("x0", 64)));
        graph = Graph(Architecture.Arm64,
            [a.Finish(MirExit.Jump(a.Const(64, 0x2004))), b.Finish(MirExit.Jump(b.Const(64, 0x2000)))], [0x2000, 0x2004]);
        foreach (var entry in new ulong[] { 0x2000, 0x2004 }) checks += Compare(graph, entry, State(Architecture.Arm64), 17);

        var first = Builder(Architecture.Arm64, 0x1000);
        first.Store(first.Const(64, 0x4000), first.Const(8, 42));
        var partial = Builder(Architecture.Arm64, 0x1004);
        partial.Write("x0", partial.Const(64, 11));
        partial.Store(partial.Const(64, 0x5000), partial.Const(128, BigInteger.One << 120), new(MemoryOrder.Relaxed, 64, 64));
        partial.Write("x1", partial.Const(64, 99));
        graph = Graph(Architecture.Arm64, [first.Finish(MirExit.Next(0x1004)), partial.Finish(MirExit.Next(0x1008))], [0x1000]);
        var partialState = State(Architecture.Arm64);
        partialState.Memory[0x4000] = 0;
        for (var i = 0; i < 15; i++) partialState.Memory[0x5000UL + (ulong)i] = 0xA5;
        checks += Compare(graph, 0x1000, partialState, 4);
        var partialResult = NativeExecutor.Execute(StateSsaConverter.Convert(graph), 0x1000, Clone(partialState), 4);
        CoreChecks.Require(partialResult.LastInstruction?.Stop is { MemoryEventStart: 1, MemoryEventCount: 2 }, "native partial stop excludes earlier instruction events");
        checks++;

        var missing = Builder(Architecture.Arm64, 0x1000);
        missing.Write("x0", missing.Const(64, 17));
        missing.Write("x1", missing.Read("x2", 64));
        graph = Graph(Architecture.Arm64, [missing.Finish(MirExit.Next(0x1004))], [0x1000]);
        checks += Compare(graph, 0x1000, new MachineState(), 2);
        var known = new MachineState();
        known.Slots["x2"] = 31;
        checks += Compare(graph, 0x1000, known, 2);

        var inactive = Builder(Architecture.Arm64, 0x1000);
        var inactiveLoad = inactive.LoadIf(inactive.Const(1, 0), inactive.Const(64, ulong.MaxValue), 64);
        inactive.Write("x0", inactiveLoad);
        inactive.StoreIf(inactive.Const(1, 0), inactive.Const(64, ulong.MaxValue), inactiveLoad);
        inactive.Guard(inactive.Const(1, 0), "fixture semantic stop", StopKind.UnmodeledSemantics);
        graph = Graph(Architecture.Arm64, [inactive.Finish(MirExit.Next(0x1004))], [0x1000]);
        checks += Compare(graph, 0x1000, State(Architecture.Arm64), 2);

        var exclusive = Builder(Architecture.Arm64, 0x1000);
        exclusive.Write("x0", exclusive.LoadExclusive(exclusive.Const(64, 0x6000), 64, new(MemoryOrder.Acquire, 64, 64)));
        var store = Builder(Architecture.Arm64, 0x1004);
        store.Write("x1", store.Zext(store.StoreExclusive(store.Const(64, 0x6000), store.Read("x0", 64), new(MemoryOrder.Release, 64, 64)), 64));
        graph = Graph(Architecture.Arm64, [exclusive.Finish(MirExit.Next(0x1004)), store.Finish(MirExit.Next(0x1008))], [0x1000]);
        foreach (var decision in new[] { false, true })
        foreach (var interfere in new[] { false, true })
        {
            var state = State(Architecture.Arm64);
            for (var i = 0; i < 8; i++) state.Memory[0x6000UL + (ulong)i] = (byte)i;
            state.ExclusiveStoreDecisions.Enqueue(decision);
            if (interfere) state.Schedule.Enqueue(new(1, 0x6000, [0xFF], true));
            checks += Compare(graph, 0x1000, state, 4);
        }

        var x64Code = new[] { "B812000000", "B034", "66B85678", "88E0", "F20F58C1", "0F28D0", "CC" };
        var x64Instructions = Decode(Architecture.X64, 0x1000, x64Code);
        graph = Graph(Architecture.X64, x64Instructions, [0x1000]);
        var random = new Random(803);
        for (var i = 0; i < 48; i++)
        {
            var state = State(Architecture.X64);
            state.Slots["rax"] = (BigInteger.One << 63) | random.NextInt64();
            state.Slots["xmm0"] = (new BigInteger(random.NextInt64()) << 64) | (ulong)BitConverter.DoubleToInt64Bits(i - 13.25);
            state.Slots["xmm1"] = (ulong)BitConverter.DoubleToInt64Bits(i + 0.125);
            checks += Compare(graph, 0x1000, state, 10);
        }
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var instructions = architecture == Architecture.Arm64
                ? Decode(architecture, 0x1000, ["20040091", "02000094", "000020D4"])
                : Decode(architecture, 0x1000, ["B811000000", "E800000000", "CC"]);
            graph = Graph(architecture, instructions, [0x1000]);
            var state = State(architecture);
            if (architecture == Architecture.X64)
            {
                state.Slots["rsp"] = 0x7008;
                for (var i = 0; i < 8; i++) state.Memory[0x7000UL + (ulong)i] = 0;
            }
            checks += Compare(graph, 0x1000, state, 5);
            var result = NativeExecutor.Execute(StateSsaConverter.Convert(graph), 0x1000, Clone(state), 5);
            CoreChecks.Require(result.Boundary?.Kind == RegionBoundaryKind.Call && result.Instructions == 2, "call does not fabricate a returning continuation");
            checks++;
        }
        return checks;
    }

    public static int Compare(RegionRevision graph, ulong entry, MachineState initial, int budget)
    {
        var native = StateSsaConverter.Convert(graph);
        var normalized = NativeNormalizer.Normalize(native);
        CoreChecks.Require(native.Blocks.SelectMany(b => b.Nodes).All(n => n.Code is not (OpCode.ReadSlot or OpCode.WriteSlot)), "SSA removes all machine-slot operations");
        var expectedState = Clone(initial);
        var actualState = Clone(initial);
        var reducedState = Clone(initial);
        var expectedTrace = new List<string>();
        var actualTrace = new List<string>();
        var reducedTrace = new List<string>();
        var expected = MirRegionExecutor.Execute(graph, entry, expectedState, budget,
            (ir, result, state) => expectedTrace.Add(Witness(ir, result, state)));
        var actual = NativeExecutor.Execute(native, entry, actualState, budget,
            (ir, result, state) => actualTrace.Add(Witness(ir, result, state)));
        var reduced = NativeExecutor.Execute(normalized, entry, reducedState, budget,
            (ir, result, state) => reducedTrace.Add(Witness(ir, result, state)));
        CoreChecks.Require(expectedTrace.SequenceEqual(actualTrace), $"MIR/SSA instruction-boundary state mismatch at 0x{entry:X}");
        CoreChecks.Require(expected.Outcome == actual.Outcome && expected.Address == actual.Address && expected.NextAddress == actual.NextAddress &&
            expected.Boundary == actual.Boundary && expected.Instructions == actual.Instructions && expected.LastInstruction == actual.LastInstruction &&
            expected.TraversedEdges.SequenceEqual(actual.TraversedEdges), "MIR/SSA final boundary and parallel edge identity");
        CoreChecks.Require(Snapshot(expectedState) == Snapshot(actualState), "MIR/SSA final external state");
        CoreChecks.Require(expectedTrace.SequenceEqual(reducedTrace), $"MIR/N2 instruction-boundary state mismatch at 0x{entry:X}");
        CoreChecks.Require(expected.Outcome == reduced.Outcome && expected.Address == reduced.Address && expected.NextAddress == reduced.NextAddress &&
            expected.Boundary == reduced.Boundary && expected.Instructions == reduced.Instructions && expected.LastInstruction == reduced.LastInstruction &&
            expected.TraversedEdges.SequenceEqual(reduced.TraversedEdges), "MIR/N2 final boundary and parallel edge identity");
        CoreChecks.Require(Snapshot(expectedState) == Snapshot(reducedState), "MIR/N2 final external state");
        return 7 + expectedTrace.Count * 2;
    }

    public static MachineState State(Architecture architecture)
    {
        var state = new MachineState();
        foreach (var (name, _) in StateLayout.For(architecture)) state.Slots[name] = 0;
        state.Slots[architecture == Architecture.X64 ? "mxcsr" : "fpcr"] = architecture == Architecture.X64 ? 0x1F80 : 0;
        state.CodeGuardedPages[1] = false;
        state.CodeGuardedPages[2] = false;
        return state;
    }

    public static MachineState Clone(MachineState source)
    {
        var state = new MachineState { Reservation = source.Reservation };
        foreach (var item in source.Slots) state.Slots.Add(item.Key, item.Value);
        foreach (var item in source.Memory) state.Memory.Add(item.Key, item.Value);
        foreach (var item in source.CodeGuardedPages) state.CodeGuardedPages.Add(item.Key, item.Value);
        foreach (var item in source.WritePermissions) state.WritePermissions.Add(item.Key, item.Value);
        state.Accesses.AddRange(source.Accesses);
        state.Events.AddRange(source.Events);
        state.ChoiceObservations.AddRange(source.ChoiceObservations);
        state.AppliedSchedule.AddRange(source.AppliedSchedule);
        foreach (var item in source.ChoiceInputs) state.ChoiceInputs.Enqueue(item);
        foreach (var item in source.ExclusiveStoreDecisions) state.ExclusiveStoreDecisions.Enqueue(item);
        foreach (var item in source.Schedule) state.Schedule.Enqueue(item);
        return state;
    }

    private static string Witness(MirInstruction ir, ExecutionResult result, MachineState state) =>
        JsonSerializer.Serialize(new { ir.Origin.Address, result, state = Snapshot(state) }, MirJson.Options);

    private static string Snapshot(MachineState state) => JsonSerializer.Serialize(new
    {
        slots = state.Slots.OrderBy(p => p.Key, StringComparer.Ordinal), memory = state.Memory.OrderBy(p => p.Key),
        state.Reservation, state.Accesses, state.Events, state.ChoiceObservations,
        choices = state.ChoiceInputs.ToArray(), decisions = state.ExclusiveStoreDecisions.ToArray(),
        schedule = state.Schedule.ToArray(), state.AppliedSchedule,
        codePages = state.CodeGuardedPages.OrderBy(p => p.Key), permissions = state.WritePermissions.OrderBy(p => p.Key)
    }, MirJson.Options);

    private static MirBuilder Builder(Architecture architecture, ulong address) =>
        new(architecture, new(ImageId, address, (long)address, new byte[4]), "fixture.native-execution");
    private static RegionRevision Graph(Architecture architecture, IEnumerable<MirInstruction> instructions, ulong[] entries) =>
        RegionBuilder.FromInstructions(architecture, ImageId, instructions, entries.Select(a => new EntrySeed(a, "synthetic control-flow fixture")), 100);

    private static ImmutableArray<MirInstruction> Decode(Architecture architecture, ulong address, string[] hex)
    {
        var instructions = ImmutableArray.CreateBuilder<MirInstruction>();
        foreach (var text in hex)
        {
            var bytes = Convert.FromHexString(text);
            var origin = new InstructionOrigin(ImageId, address, (long)address, bytes);
            LiftResult lifted;
            if (architecture == Architecture.Arm64) lifted = Arm64Lifter.Lift(origin);
            else
            {
                var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes));
                decoder.IP = address;
                lifted = X64Lifter.Lift(origin, decoder.Decode());
            }
            CoreChecks.Require(lifted.Ir is not null, "native machine-code fixture must lift");
            instructions.Add(lifted.Ir!);
            address += (ulong)bytes.Length;
        }
        return instructions.ToImmutable();
    }
}
