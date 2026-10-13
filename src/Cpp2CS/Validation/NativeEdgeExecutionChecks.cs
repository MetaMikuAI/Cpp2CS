using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

public static class NativeEdgeExecutionChecks
{
    private const string ImageId = "fixture:native-edge-execution";

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }

        var swap = Builder(0x1000);
        var originalX0 = swap.Read("x0", 64);
        var originalX1 = swap.Read("x1", 64);
        swap.Write("x0", originalX1);
        swap.Write("x1", originalX0);
        var remaining = swap.Sub(swap.Read("x9", 64), swap.Const(64, 1));
        swap.Write("x9", remaining);
        var swapIr = swap.Finish(MirExit.Branch(swap.Eq(remaining, swap.Const(64, 0)),
            swap.Const(64, 0x1004), swap.Const(64, 0x1000)));
        var exit = Builder(0x1004);
        exit.Write("x3", exit.Read("x0", 64));
        var graph = Graph([swapIr, exit.Finish(MirExit.Next(0x1008))]);
        for (var iterations = 1; iterations <= 8; iterations++)
        {
            var initial = NativeExecutionChecks.State(Architecture.Arm64);
            initial.Slots["x0"] = 11;
            initial.Slots["x1"] = 29;
            initial.Slots["x9"] = iterations;
            checks += NativeExecutionChecks.Compare(graph, 0x1000, initial, iterations + 2);
            var state = NativeExecutionChecks.Clone(initial);
            var result = NativeExecutor.Execute(StateSsaConverter.Convert(graph), 0x1000, state, iterations + 2);
            var odd = (iterations & 1) != 0;
            Check(state.ReadSlot("x0") == (odd ? 29 : 11) && state.ReadSlot("x1") == (odd ? 11 : 29) &&
                state.ReadSlot("x3") == state.ReadSlot("x0") && state.ReadSlot("x9") == 0,
                "backedge slot exchange binds both parameters from their original values");
            Check(result.Instructions == iterations + 1 && result.LastInstruction?.Status == ExecutionOutcome.Normal,
                "slot exchange reaches the exit after the requested number of iterations");
        }

        var branch = Builder(0x1000);
        var branchIr = branch.Finish(MirExit.Branch(branch.Read("z", 1), branch.Const(64, 0x1004), branch.Const(64, 0x1008)));
        var defined = Builder(0x1004);
        defined.Write("x2", defined.Const(64, 31));
        var absent = Builder(0x1008);
        absent.Write("x1", absent.Const(64, 5));
        var join = Builder(0x100C);
        join.Write("x0", join.Const(64, 17));
        join.Write("x3", join.Read("x2", 64));
        var joinIr = join.Finish(MirExit.Next(0x1010));
        graph = Graph([branchIr, defined.Finish(MirExit.Jump(defined.Const(64, 0x100C))),
            absent.Finish(MirExit.Next(0x100C)), joinIr]);
        foreach (var takeDefinition in new[] { false, true })
        {
            var initial = new MachineState();
            initial.Slots["z"] = takeDefinition ? 1 : 0;
            initial.Slots["x3"] = 77;
            checks += NativeExecutionChecks.Compare(graph, 0x1000, initial, 5);
            var state = NativeExecutionChecks.Clone(initial);
            var result = NativeExecutor.Execute(StateSsaConverter.Convert(graph), 0x1000, state, 5);
            Check(result.Instructions == 3 && state.ReadSlot("x0") == 17,
                "a missing entry slot traverses the selected branch and stops only when actually read");
            if (takeDefinition)
                Check(result.LastInstruction?.Status == ExecutionOutcome.Normal && state.ReadSlot("x2") == 31 && state.ReadSlot("x3") == 31,
                    "a branch definition replaces a missing slot before the join reads it");
            else
                Check(result.Outcome == RegionRunOutcome.ExecutionStop && result.Address == 0x100C &&
                    result.LastInstruction?.Stop is { Kind: StopKind.MissingEnvironment, OperationIndex: 2, CompletedStateToken.Id: 1 } &&
                    !state.Slots.ContainsKey("x2") && state.ReadSlot("x3") == 77,
                    "an undefined incoming slot remains missing at the join and preserves the completed prefix");
        }

        var seed = Builder(0x1000);
        seed.Store(seed.Const(64, 0x4000), seed.Const(8, 42));
        var guarded = Builder(0x1004);
        var before = guarded.Undefined(8, "choice before semantic stop");
        guarded.Write("x0", guarded.Zext(before, 64));
        guarded.Guard(guarded.Const(1, 0), "choice boundary", StopKind.UnmodeledSemantics);
        guarded.Write("x1", guarded.Zext(guarded.Undefined(8, "choice after semantic stop"), 64));
        graph = Graph([seed.Finish(MirExit.Next(0x1004)), guarded.Finish(MirExit.Next(0x1008))]);
        var choiceInitial = NativeExecutionChecks.State(Architecture.Arm64);
        choiceInitial.Memory[0x4000] = 0;
        choiceInitial.Slots["x1"] = 99;
        foreach (var value in new[] { 5, 7, 9 }) choiceInitial.ChoiceInputs.Enqueue(value);
        checks += NativeExecutionChecks.Compare(graph, 0x1000, choiceInitial, 4);
        var choiceState = NativeExecutionChecks.Clone(choiceInitial);
        var choiceResult = NativeExecutor.Execute(StateSsaConverter.Convert(graph), 0x1000, choiceState, 4);
        Check(choiceResult.Instructions == 2 && choiceResult.LastInstruction?.Choices == 1 &&
            choiceResult.LastInstruction.Stop is { Kind: StopKind.UnmodeledSemantics, CompletedStateToken.Id: 2, MemoryEventStart: 1, MemoryEventCount: 0 },
            "a stop after a choice reports its completed state without consuming earlier memory events");
        Check(choiceState.ChoiceInputs.SequenceEqual(new BigInteger[] { 7, 9 }) &&
            choiceState.ChoiceObservations is [{ Sequence: 0, InstructionAddress: 0x1004, OperationIndex: 0, IsExplicit: true }] &&
            choiceState.ChoiceObservations[0].Result == before && choiceState.ChoiceObservations[0].Bits == 5,
            "only the choice preceding a failed guard consumes an input and records its original site");
        Check(choiceState.ReadSlot("x0") == 5 && choiceState.ReadSlot("x1") == 99 && choiceState.Events.Count == 1,
            "a failed guard retains preceding writes and excludes subsequent choices and writes");
        return checks;
    }

    private static MirBuilder Builder(ulong address) =>
        new(Architecture.Arm64, new(ImageId, address, (long)address, new byte[4]), "fixture.native-edge-execution");

    private static RegionRevision Graph(IEnumerable<MirInstruction> instructions) =>
        RegionBuilder.FromInstructions(Architecture.Arm64, ImageId, instructions,
            [new EntrySeed(0x1000, "synthetic edge-execution fixture")], 100);
}
