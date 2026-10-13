using Cpp2CS.Ir;

namespace Cpp2CS.Validation;

public static class MirInspectionChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string message) { CoreChecks.Require(condition, message); checks++; }
        var origin = new InstructionOrigin("fixture:inspection", 0x1000, 0, new byte[] { 0x90 });
        var b = new MirBuilder(Architecture.X64, origin, "fixture.dependencies");
        var old = b.Read("rax", 64);
        b.Write("rax", b.Add(old, b.Const(64, 1)));
        var next = b.Read("rax", 64);
        b.Undefined(1, "independent architectural choice");
        b.LoadIf(b.Const(1, 0), next, 8);
        var instruction = b.Finish(MirExit.Branch(b.Const(1, 1), next, next));
        var view = MirInspection.Describe(instruction);
        Check(view.Origin == origin && view.Rule == instruction.Rule, "inspection retains origin and rule");
        Check(view.Profile.Id == instruction.ProfileId, "inspection binds the validated profile");
        Check(view.StateAccesses.Length == 3, "full canonical state dependencies remain explicit");
        Check(view.StateAccesses.Select(item => item.Kind).SequenceEqual(new[] { SlotAccessKind.Read, SlotAccessKind.Write, SlotAccessKind.Read }),
            "state dependency order is preserved");
        Check(view.StateAccesses.All(item => item.Slot == "rax" && item.Width == 64), "partial views do not invent alias storage");
        Check(view.Effects.Length == 5 && view.Effects[^1].Flow.Output == instruction.FinalState, "all state, choice and memory dependencies are ordered");
        Check(view.Effects.Any(item => item.Code == OpCode.Undefined && item.Effects.HasFlag(OperationEffects.Choice)),
            "unused choice is not classified as pure");
        Check(view.Effects.Single(item => item.Code == OpCode.LoadIf).Inputs[0].Width == 1,
            "conditional access retains its predicate");
        Check(view.Successors.Length == 2, "parallel branch edges are not coalesced");
        Check(view.Successors[0].Condition is { RequiredValue: true } && view.Successors[1].Condition is { RequiredValue: false },
            "branch edge predicates remain distinct");
        Check(view.Successors.All(item => item.Destination == new ValueDestination(next) && item.State == instruction.FinalState),
            "successors retain computed target and final machine state");
        Check(view.Capabilities.NormalTransitionRepresented && view.Capabilities.HasChoices && view.Capabilities.MayStopBeforeExit,
            "capabilities separate normal transition, choice and possible stops");
        Check(!view.Capabilities.FaultDeliveryModeled && !view.Capabilities.ConcurrentExecutionsVerified,
            "inspection does not invent semantic validation evidence");
        Check(view.Capabilities.Obligations.Any(item => item.Kind == ObligationKind.FaultDelivery), "conditional memory retains its obligation even for constant false");

        b.Write("rcx", next);
        Check(MirInspection.Describe(instruction).Effects.Length == 5, "finished instructions are immutable builder snapshots");
        var state = new MachineState();
        state.Slots["rax"] = 10;
        var execution = MirInterpreter.Execute(instruction, state);
        Check(execution.NextAddress == 11 && state.Slots["rax"] == 11, "read after write observes the new slot value");
        Check(state.Events.Count == 0 && execution.CompletedStateToken.Id == 5, "ordered tokens do not imply runtime memory events");

        var trap = new MirBuilder(Architecture.X64, origin, "fixture.exception").Finish(
            MirExit.Trap(ExceptionKind.X64Breakpoint, "x64.#BP", 0x1001));
        var trapView = MirInspection.Describe(trap);
        Check(trapView.Successors is [{ Kind: SuccessorKind.ExceptionBoundary, Destination: ExceptionDestination }],
            "exception boundary has no fabricated normal successor");
        Check(!trapView.Capabilities.NormalTransitionRepresented && trapView.Capabilities.ExceptionBoundaryRepresented,
            "exception event is separate from normal semantics");
        Check(trapView.Capabilities.Support == SupportClass.ExceptionBoundaryOnly, "exception support is derived");

        var memory = new MirBuilder(Architecture.Arm64, new("fixture:memory-dependencies", 0x2000, 0, new byte[4]), "fixture.memory-query");
        var address = memory.Const(64, 0x3000);
        var load64 = memory.Load(address, 64, new(MemoryOrder.Acquire, 64, 64));
        var load128 = memory.LoadExclusive(address, 128, new(MemoryOrder.Relaxed, 64, 64));
        memory.Store(address, load64);
        var memoryView = MirInspection.Describe(memory.Finish(MirExit.Next(0x2004)));
        Check(memoryView.Effects[0].Result == load64 && memoryView.Effects[0].Result!.Value.Width == 64,
            "load query exposes result identity and total access width");
        Check(memoryView.Effects[1].Result == load128 && memoryView.Effects[1].Result!.Value.Width == 128,
            "exclusive pair result preserves full width rather than beat width");
        Check(memoryView.Effects[0].Effects.HasFlag(OperationEffects.Ordering), "acquire memory exposes payload-dependent ordering");
        Check(memoryView.Effects[2].Effects.HasFlag(OperationEffects.ReadMonitor | OperationEffects.WriteMonitor),
            "ordinary store query includes reservation invalidation");
        return checks;
    }
}
