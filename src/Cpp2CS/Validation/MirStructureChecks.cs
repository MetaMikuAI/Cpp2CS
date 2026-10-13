using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Validation;

public static class MirStructureChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        void Invalid(MirInstruction ir, string reason) => Check(MirValidator.Validate(ir).Count != 0, reason);
        var origin = new InstructionOrigin("fixture:structure", 0x1000, 0, new byte[4]);
        var b = new MirBuilder(Architecture.Arm64, origin, "fixture.state-order");
        var before = b.Read("x0", 64);
        var sum = b.Add(before, b.Const(64, 1));
        b.Write("x0", sum);
        var after = b.Read("x0", 64);
        var choice = b.Undefined(64, "fixture architectural choice");
        b.Write("x1", b.Xor(after, choice));
        b.Load(b.Const(64, 0x4000), 64);
        var ir = b.Finish(MirExit.Next(0x1004));
        Check(MirValidator.Validate(ir).Count == 0, "mixed state, choice and memory operations validate");
        Check(ir.FinalState.Id == 6, "final state includes slot reads, writes, choice and memory");
        Check(ir.Operations.Where(op => op.Flow is not null).Select(op => op.Flow!.Input.Id).SequenceEqual(Enumerable.Range(0, 6)), "all state actions form one ordered chain");
        Check((ir with { Annotations = [] }).Support == SupportClass.NormalPathOnly, "memory limitation is derived independently of annotations");
        Check(MirJson.Serialize(MirJson.Deserialize(MirJson.Serialize(ir))) == MirJson.Serialize(ir), "typed operation roundtrip is stable");

        for (var index = 0; index < ir.Operations.Length; index++)
        {
            var op = ir.Operations[index];
            var wrongPayload = op.Payload is NoPayload ? (OperationPayload)new ImmediatePayload(0) : NoPayload.Instance;
            Invalid(ir with { Operations = ir.Operations.SetItem(index, op with { Payload = wrongPayload }) }, "opcode rejects another payload variant");
            if (op.Flow is { } flow)
            {
                Invalid(ir with { Operations = ir.Operations.SetItem(index, op with { Flow = null }) }, "state action cannot lose its dependency");
                Invalid(ir with { Operations = ir.Operations.SetItem(index, op with { Flow = new(flow.Input, flow.Input) }) }, "state action cannot reuse its input token as output");
                Invalid(ir with { Operations = ir.Operations.SetItem(index, op with { Flow = new(new(flow.Input.Id + 1), flow.Output) }) }, "state action cannot skip its predecessor");
            }
            else
                Invalid(ir with { Operations = ir.Operations.SetItem(index, op with { Flow = new(new(0), new(1)) }) }, "pure operation cannot acquire a state edge");
        }
        Invalid(ir with { Exit = ir.Exit with { State = new(ir.FinalState.Id - 1) } }, "exit must consume the final state");
        Invalid(ir with { Operations = default }, "default operation collection is not an empty program");
        Invalid(ir with { Annotations = default }, "default annotation collection is rejected");
        Invalid(ir with { ProfileId = MachineProfile.For(Architecture.X64).Id }, "profile is part of instruction identity");
        Invalid(ir with { Architecture = (Architecture)999 }, "unknown architecture is a validation diagnostic");
        var first = ir.Operations[0];
        Invalid(ir with { Operations = ir.Operations.SetItem(0, first with { Code = (OpCode)999 }) }, "every opcode requires a registered specification");
        Invalid(ir with { Operations = ir.Operations.SetItem(0, first with { Inputs = default }) }, "default input collection is rejected");
        Invalid(ir with { Annotations = [new((ObligationKind)999, "invalid obligation")] }, "obligation kind is closed");
        Invalid(ir with { Annotations = [new(ObligationKind.PartialState, "invalid location", ir.Operations.Length)] }, "obligation location must refer to a real operation");

        var originals = new[] { new Value(0, 64), new Value(1, 64) };
        var snapshot = new Operation(OpCode.Add, new(2, 64), originals.ToImmutableArray(), NoPayload.Instance);
        originals[0] = new(999, 1);
        Check(snapshot.Inputs[0] == new Value(0, 64), "operation input snapshot cannot follow external array mutation");
        foreach (var code in Enum.GetValues<OpCode>())
            Check(OperationSpecs.TryGet(code, out var spec) && spec.Arity >= 0 && typeof(OperationPayload).IsAssignableFrom(spec.PayloadType), "every opcode exposes a closed operation contract");
        foreach (var code in new[] { OpCode.Store, OpCode.StoreIf, OpCode.AtomicRmw })
            Check(OperationSpecs.For(code).Effects.HasFlag(OperationEffects.ReadMonitor | OperationEffects.WriteMonitor), "writing memory retains possible reservation inspection and invalidation");
        Check(OperationSpecs.For(OpCode.StoreExclusive).Effects.HasFlag(OperationEffects.ReadMonitor | OperationEffects.WriteMonitor), "exclusive store reads and updates reservation state");
        Check(OperationSpecs.For(OpCode.ReadSlot).Effects.HasFlag(OperationEffects.ReadSlot) &&
            !OperationSpecs.For(OpCode.ReadSlot).Effects.HasFlag(OperationEffects.ReadMonitor), "slot reads and monitor access have distinct categories");
        Check(OperationSpecs.For(OpCode.LoadExclusive).Effects.HasFlag(OperationEffects.WriteMonitor), "exclusive load establishes reservation state");
        foreach (var code in new[] { OpCode.Load, OpCode.Store, OpCode.LoadIf, OpCode.StoreIf, OpCode.LoadExclusive,
                     OpCode.StoreExclusive, OpCode.ClearExclusive, OpCode.Barrier, OpCode.Prefetch, OpCode.WriteProbe, OpCode.AtomicRmw })
            Check(OperationSpecs.For(code).Effects.HasFlag(OperationEffects.Environment), "scheduled memory events retain an environment dependency");
        Check(OperationSpecs.For(OpCode.AtomicRmw).Effects.HasFlag(OperationEffects.Ordering), "locked RMW is an ordering event");
        var ordinaryLoad = ir.Operations.Single(op => op.Code == OpCode.Load);
        var orderedLoad = ordinaryLoad with { Payload = new MemoryPayload(new(MemoryOrder.Acquire, 64, 64)) };
        Check(!OperationSpecs.EffectiveEffects(ordinaryLoad).HasFlag(OperationEffects.Ordering), "ordinary relaxed load does not gain acquire ordering");
        Check(OperationSpecs.EffectiveEffects(orderedLoad).HasFlag(OperationEffects.Ordering), "effective effects include payload memory ordering");

        foreach (var kind in Enum.GetValues<StopKind>())
        {
            var guard = new MirBuilder(Architecture.Arm64, origin, "fixture.guard-kind");
            guard.Guard(guard.Const(1, 0), "explicit stop reason", kind);
            var guarded = guard.Finish(MirExit.Next(0x1004));
            Check(MirValidator.Validate(guarded).Count == 0, "each stop kind is a valid explicit guard contract");
            var index = guarded.Operations.Length - 1;
            Invalid(guarded with { Operations = guarded.Operations.SetItem(index,
                guarded.Operations[index] with { Payload = new GuardPayload((StopKind)999, "invalid kind") }) }, "unknown stop kind is rejected");
        }

        foreach (var kind in Enum.GetValues<ExceptionKind>())
        {
            var architecture = kind == ExceptionKind.ArmBreakpoint ? Architecture.Arm64 : Architecture.X64;
            var saved = kind is ExceptionKind.X64Breakpoint or ExceptionKind.X64Debug ? 0x1004UL : 0x1000UL;
            ushort? syndrome = kind switch { ExceptionKind.ArmBreakpoint => 0x1234, ExceptionKind.X64GeneralProtection => 0, _ => null };
            var trap = new MirBuilder(architecture, origin, "fixture.exception").Finish(MirExit.Trap(kind, "fixture event", saved, syndrome));
            Check(MirValidator.Validate(trap).Count == 0, "structured exception boundary validates");
            var exit = (TrapExit)trap.Exit;
            Invalid(trap with { Exit = exit with { Boundary = exit.Boundary with { SavedAddress = saved + 1 } } }, "exception saved address follows its kind");
            Invalid(trap with { Exit = exit with { Boundary = exit.Boundary with { Syndrome = syndrome is null ? (ushort)1 : kind == ExceptionKind.X64GeneralProtection ? (ushort)1 : null } } }, "exception syndrome follows its kind");
            Invalid(trap with { Exit = exit with { Boundary = exit.Boundary with { Detail = "" } } }, "exception description is required");
        }
        return checks;
    }
}
