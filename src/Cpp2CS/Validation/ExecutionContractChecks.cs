using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Validation;

public static class ExecutionContractChecks
{
    private static readonly InstructionOrigin Origin = new("fixture:execution-contract", 0x1000, 0, new byte[4]);
    private const ulong Address = 0x4000;

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        MirInstruction Finish(MirBuilder builder) => MirJson.Deserialize(MirJson.Serialize(builder.Finish(MirExit.Next(0x1004))));

        var missing = new MirBuilder(Architecture.Arm64, Origin, "fixture.missing-slot");
        missing.Write("x0", missing.Const(64, 11));
        missing.Write("x1", missing.Read("x2", 64));
        var missingIr = Finish(missing);
        var missingState = new MachineState();
        missingState.Slots["x1"] = 17;
        var result = MirInterpreter.Execute(missingIr, missingState);
        var readIndex = Array.FindIndex(missingIr.Operations.ToArray(), op => op.Code == OpCode.ReadSlot);
        Check(result.Status == ExecutionOutcome.UnmodeledEnvironmentStop && result.Stop?.Kind == StopKind.MissingEnvironment,
            "missing slot is an environment stop");
        Check(result.Stop?.OperationIndex == readIndex && result.Stop.CompletedStateToken == new StateToken(1),
            "missing slot reports its operation and completed state prefix");
        Check(missingState.ReadSlot("x0") == 11 && missingState.ReadSlot("x1") == 17 && !missingState.Slots.ContainsKey("x2"),
            "missing slot preserves prior writes and stops subsequent writes without fabricating a value");
        Check(result.StateKind == ExecutionStateKind.CompletedPrefixWitness && result.NextAddress is null && result.Exception is null,
            "missing slot does not claim a successor or architectural exception");

        foreach (var (kind, outcome) in new[]
        {
            (StopKind.FaultBoundary, ExecutionOutcome.UnmodeledFaultStop),
            (StopKind.MissingEnvironment, ExecutionOutcome.UnmodeledEnvironmentStop),
            (StopKind.UnmodeledSemantics, ExecutionOutcome.UnmodeledSemanticsStop)
        })
        foreach (var satisfied in new[] { false, true })
        {
            var guard = new MirBuilder(Architecture.Arm64, Origin, "fixture.guard-kind");
            guard.Guard(guard.Const(1, satisfied ? 1UL : 0UL), "same detail for distinct kinds", kind);
            guard.Write("x0", guard.Const(64, 99));
            var ir = Finish(guard);
            var state = new MachineState();
            state.Slots["x0"] = 17;
            result = MirInterpreter.Execute(ir, state);
            Check(result.Status == (satisfied ? ExecutionOutcome.Normal : outcome), "guard status follows its typed kind");
            Check(satisfied ? result.Stop is null : result.Stop?.Kind == kind, "guard detail text does not classify its stop");
            Check(state.ReadSlot("x0") == (satisfied ? 99 : 17) && state.Events.Count == 0,
                "guard controls later slot writes without generating a memory event");
            Check(result.CompletedStateToken == (satisfied ? ir.FinalState : new StateToken(0)),
                "failed guard does not commit its state output token");
            Check(satisfied ? result.StateKind == ExecutionStateKind.NormalSuccessor && result.NextAddress == 0x1004
                    : result.StateKind == ExecutionStateKind.CompletedPrefixWitness && result.NextAddress is null,
                "normal successor and stopped prefix are distinct results");
        }

        var choice = new MirBuilder(Architecture.Arm64, Origin, "fixture.choice-occurrences");
        var first = choice.Undefined(8, "architecturally unspecified bits");
        var second = choice.Undefined(8, "architecturally unspecified bits");
        choice.Write("x0", choice.Zext(first, 64));
        choice.Write("x1", choice.Zext(second, 64));
        choice.Write("x2", choice.Zext(choice.Add(first, first), 64));
        var choiceIr = Finish(choice);
        var choiceState = new MachineState();
        foreach (var bits in new[] { 5, 7, 9, 11 }) choiceState.ChoiceInputs.Enqueue(bits);
        for (var invocation = 0; invocation < 2; invocation++)
        {
            result = MirInterpreter.Execute(choiceIr, choiceState);
            Check(result.Status == ExecutionOutcome.Normal && result.Choices == 2, "each execution observes both choice occurrences");
            Check(choiceState.ReadSlot("x0") == 5 + invocation * 4 && choiceState.ReadSlot("x1") == 7 + invocation * 4,
                "distinct occurrences may differ and later execution gets fresh choices");
            Check(choiceState.ReadSlot("x2") == 2 * choiceState.ReadSlot("x0"), "reusing a choice value observes one stable occurrence");
            Check(choiceState.ChoiceInputs.Count == 2 - invocation * 2, "only executed choices consume supplied inputs");
        }
        Check(choiceState.ChoiceObservations.Select(item => item.Sequence).SequenceEqual(new[] { 0, 1, 2, 3 }),
            "choice trace preserves dynamic occurrence order");
        Check(choiceState.ChoiceObservations.All(item => item.IsExplicit && item.InstructionAddress == Origin.Address && item.Result.Width == 8),
            "explicit choice trace carries the instruction site and width");
        Check(choiceState.ChoiceObservations[0].Result == choiceState.ChoiceObservations[2].Result &&
            choiceState.ChoiceObservations[0].Bits != choiceState.ChoiceObservations[2].Bits,
            "the same static choice site can differ across executions");
        var zeroWitness = new MachineState();
        result = MirInterpreter.Execute(choiceIr, zeroWitness);
        Check(result.ChoicePolicy == ChoicePolicy.ExplicitInputsThenZeroWitness && result.Choices == 2,
            "default choice policy is explicit in the result");
        Check(zeroWitness.ChoiceObservations.All(item => !item.IsExplicit && item.Bits.IsZero) && zeroWitness.ReadSlot("x2").IsZero,
            "zero defaults are marked as witness choices rather than supplied facts");

        foreach (var stopAtEnd in new[] { false, true })
        {
            var ordered = new MirBuilder(Architecture.Arm64, Origin, "fixture.state-versus-event-order");
            ordered.Read("x0", 64);
            ordered.Guard(ordered.Const(1, 1), "satisfied guard");
            ordered.CodeGuarded(ordered.Const(64, Origin.Address));
            var inactive = ordered.LoadIf(ordered.Const(1, 0), ordered.Const(64, ulong.MaxValue), 64);
            ordered.StoreIf(ordered.Const(1, 0), ordered.Const(64, ulong.MaxValue), inactive);
            ordered.Write("x1", inactive);
            if (stopAtEnd) ordered.Guard(ordered.Const(1, 0), "semantic boundary", StopKind.UnmodeledSemantics);
            var ir = Finish(ordered);
            var state = new MachineState();
            state.Slots["x0"] = 17;
            state.Slots["x1"] = 23;
            state.CodeGuardedPages[Origin.Address >> 12] = false;
            state.Memory[Address] = 0xA5;
            state.Schedule.Enqueue(new(0, Address, [0xFE], true));
            result = MirInterpreter.Execute(ir, state);
            Check(result.Status == (stopAtEnd ? ExecutionOutcome.UnmodeledSemanticsStop : ExecutionOutcome.Normal),
                "non-memory effects retain state flow on both outcomes");
            Check(result.CompletedStateToken == new StateToken(6) && state.Events.Count == 0 && state.Accesses.Count == 0,
                "six completed state effects do not require six memory events");
            Check(state.Schedule.Count == 1 && state.AppliedSchedule.Count == 0 && state.Memory[Address] == 0xA5 && state.ReadSlot("x1") == 0,
                "inactive memory and page lookup do not consume an event schedule");
            Check(stopAtEnd ? result.Stop?.MemoryEventCount == 0 : result.CompletedStateToken == ir.FinalState,
                "stop boundary and normal exit consume the correct state token");
        }

        var page = new MirBuilder(Architecture.Arm64, Origin, "fixture.missing-code-page");
        page.CodeGuarded(page.Const(64, Origin.Address));
        page.Write("x0", page.Const(64, 99));
        var pageState = new MachineState();
        pageState.Slots["x0"] = 17;
        result = MirInterpreter.Execute(Finish(page), pageState);
        Check(result.Stop?.Kind == StopKind.MissingEnvironment && result.CompletedStateToken == new StateToken(0),
            "page lookup stops before its output state when an environment input is missing");
        Check(pageState.ReadSlot("x0") == 17 && pageState.Events.Count == 0, "missing page lookup does not commit state or memory events");

        var partial = new MirBuilder(Architecture.Arm64, Origin, "fixture.partial-memory-prefix");
        partial.Write("x0", partial.Const(64, 11));
        partial.Store(partial.Const(64, Address), partial.Const(128, (new BigInteger(0xFFEEDDCCBBAA9988UL) << 64) | 0x1122334455667788UL),
            new(MemoryOrder.Relaxed, 64, 64));
        partial.Write("x1", partial.Const(64, 99));
        var partialIr = Finish(partial);
        var partialState = new MachineState();
        partialState.Slots["x1"] = 17;
        for (var i = 0; i < 15; i++) partialState.Memory[Address + (ulong)i] = 0xA5;
        var seed = new MirBuilder(Architecture.Arm64, Origin, "fixture.previous-instruction-event");
        seed.Store(seed.Const(64, Address), seed.Const(8, 0xA5));
        var seeded = MirInterpreter.Execute(Finish(seed), partialState);
        Check(seeded.Status == ExecutionOutcome.Normal && partialState.Events.Count == 1,
            "shared machine state retains an event from an earlier instruction");
        var laterGuard = new MirBuilder(Architecture.Arm64, Origin, "fixture.guard-after-event");
        laterGuard.Guard(laterGuard.Const(1, 0), "guard after a completed instruction");
        result = MirInterpreter.Execute(Finish(laterGuard), partialState);
        Check(result.Stop?.MemoryEventStart == 1 && result.Stop.MemoryEventCount == 0 && partialState.Events.Count == 1,
            "guard failure after an earlier event reports an empty event interval");
        result = MirInterpreter.Execute(partialIr, partialState);
        Check(result.Status == ExecutionOutcome.UnmodeledFaultStop && result.Stop?.Kind == StopKind.FaultBoundary,
            "a later beat failure remains a typed fault boundary");
        Check(result.CompletedStateToken == new StateToken(1) && result.Stop?.MemoryEventStart == 1 && result.Stop.MemoryEventCount == 2,
            "partial memory operation has no completed output token but retains both event records");
        Check(partialState.Events is [{ Outcome: "Completed" }, { Outcome: "Completed" }, { Outcome: "UnmodeledFaultStop" }] &&
            partialState.ReadSlot("x0") == 11 && partialState.ReadSlot("x1") == 17,
            "stopped prefix preserves the earlier slot write and completed memory beat");
        Check(Enumerable.Range(0, 8).All(i => partialState.Memory[Address + (ulong)i] == (byte)(0x1122334455667788UL >> (i * 8))) &&
            Enumerable.Range(8, 7).All(i => partialState.Memory[Address + (ulong)i] == 0xA5),
            "partial witness does not roll back the first beat or partially commit the faulted beat");
        Check(result.StateKind == ExecutionStateKind.CompletedPrefixWitness && result.NextAddress is null,
            "partial witness is not advertised as a normal successor or delivered exception state");

        var detachedAdd = new Operation(OpCode.Add, new Value(2000, 8), [new Value(900, 8), new Value(1200, 8)], NoPayload.Instance);
        var kernelState = new MachineState();
        var evaluation = MirOperationEvaluator.Evaluate(Architecture.Arm64, detachedAdd, [254, 3], kernelState, Origin, 37);
        Check(evaluation.Bits == 1 && evaluation.Stop is null && evaluation.Choices == 0,
            "operation kernel takes ordered input bits without interpreting local value identifiers and masks the result");
        var detachedChoice = new Operation(OpCode.Undefined, new Value(3000, 8), [], new ChoicePayload("kernel choice"));
        kernelState.ChoiceInputs.Enqueue(0xA5);
        evaluation = MirOperationEvaluator.Evaluate(Architecture.Arm64, detachedChoice, [], kernelState, Origin, 41);
        Check(evaluation.Bits == 0xA5 && evaluation.Choices == 1 && evaluation.Stop is null &&
            kernelState.ChoiceObservations is [{ OperationIndex: 41, Result.Id: 3000, IsExplicit: true }],
            "operation kernel preserves the original choice site without requiring an instruction-local values array");

        var observed = new MirBuilder(Architecture.Arm64, Origin, "fixture.observed-branch-predicate");
        var wrapped = observed.Add(observed.Const(8, 254), observed.Const(8, 3));
        var predicate = observed.Eq(wrapped, observed.Const(8, 1));
        var destination = observed.Const(64, 0x2000);
        var observedIr = observed.Finish(MirExit.Branch(predicate, destination, destination));
        var observations = new Dictionary<Value, BigInteger>();
        result = MirInterpreter.Execute(observedIr, new MachineState(), (value, bits) => observations.Add(value, bits));
        Check(result.NextAddress == 0x2000 && observations[wrapped] == 1 && observations[predicate] == 1,
            "value observations expose the masked branch predicate even when both successors share an address");
        observations.Clear();
        result = MirInterpreter.Execute(partialIr, new MachineState(), (value, bits) => observations.Add(value, bits));
        Check(result.Status == ExecutionOutcome.UnmodeledFaultStop && observations.Count == 3,
            "value observations stop at the failing operation and do not report later values");
        return checks;
    }
}
