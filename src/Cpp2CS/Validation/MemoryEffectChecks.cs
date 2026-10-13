using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Validation;

public static class MemoryEffectChecks
{
    private const ulong Address = 0x4000;
    private static readonly InstructionOrigin Origin = new("fixture:memory-effects", 0x1000, 0, new byte[4]);

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        MirInstruction Finish(MirBuilder builder)
        {
            var ir = MirJson.Deserialize(MirJson.Serialize(builder.Finish(MirExit.Next(0x1004))));
            Check(MirValidator.Validate(ir).Count == 0, "memory fixture validates and roundtrips");
            return ir;
        }

        var store = new MirBuilder(Architecture.Arm64, Origin, "fixture.exclusive-store");
        var data = (BigInteger.One << 127) | 0x12345678;
        var status = store.StoreExclusive(store.Const(64, Address), store.Const(128, data), new(MemoryOrder.Release, 64, 128));
        store.Write("x0", store.Zext(status, 64));
        store.Write("x1", store.Const(64, 99UL));
        var storeIr = Finish(store);
        var missingDecision = State(16);
        missingDecision.Reservation = new(Address, 16);
        var execution = MirInterpreter.Execute(storeIr, missingDecision);
        Check(execution.Outcome == "UnmodeledEnvironmentStop", "exclusive decision is required");
        Check(missingDecision.ReadSlot("x0") == 17 && missingDecision.ReadSlot("x1") == 23, "missing decision stops register commits");
        Check(missingDecision.Reservation == new ExclusiveReservation(Address, 16), "missing decision does not consume reservation");
        Check(missingDecision.Memory.Values.All(value => value == 0xA5) && missingDecision.Accesses.Count == 0, "missing decision does not touch memory");
        Check(missingDecision.Events is [{ Kind: "StoreExclusive", Outcome: "UnmodeledEnvironmentStop", AtomicWidth: 128 }], "missing decision retains event boundary");

        foreach (var decision in new[] { false, true })
        foreach (var reservation in new ExclusiveReservation?[] { null, new(Address + 8, 16), new(Address, 8), new(Address, 16) })
        {
            var state = State(16);
            state.Reservation = reservation;
            state.ExclusiveStoreDecisions.Enqueue(decision);
            execution = MirInterpreter.Execute(storeIr, state);
            var success = decision && reservation == new ExclusiveReservation(Address, 16);
            Check(execution.Outcome == "Normal" && state.ReadSlot("x0") == (success ? 0 : 1) && state.ReadSlot("x1") == 99, "exclusive success requires matching reservation and decision");
            Check(state.Reservation is null && state.ExclusiveStoreDecisions.Count == 0, "exclusive attempt consumes decision and reservation");
            Check(state.Events.Count == 1 && state.Events[0].Outcome == (success ? "Completed" : "Failed") && state.Events[0].AtomicWidth == 128, "pair exclusive store is one event");
            Check(success ? Read(state, 16) == data : state.Memory.Values.All(value => value == 0xA5) && state.Accesses.Count == 0, "failed store is not a memory write");
        }
        foreach (var missingByte in new[] { false, true })
        {
            var state = State(16);
            if (missingByte) state.Memory.Remove(Address + 15);
            else state.WritePermissions[Address + 15] = false;
            state.Reservation = new(Address, 16);
            state.ExclusiveStoreDecisions.Enqueue(true);
            execution = MirInterpreter.Execute(storeIr, state);
            Check(execution.Outcome == "UnmodeledFaultStop", "atomic store checks complete range");
            Check(state.Memory.Values.All(value => value == 0xA5) && state.ReadSlot("x0") == 17 && state.ReadSlot("x1") == 23, "atomic store fault has no partial data or status commit");
            Check(state.Events is [{ Outcome: "UnmodeledFaultStop", SizeBytes: 16 }], "atomic store fault remains a single event");
        }

        var load = new MirBuilder(Architecture.Arm64, Origin, "fixture.exclusive-load");
        load.Write("v0", load.LoadExclusive(load.Const(64, Address), 128, new(MemoryOrder.Acquire, 64, 64)));
        var loadIr = Finish(load);
        var split = State(16);
        split.Schedule.Enqueue(new(1, Address + 8, Enumerable.Repeat((byte)0x5A, 8).ToArray(), false));
        execution = MirInterpreter.Execute(loadIr, split);
        Check(execution.Outcome == "Normal" && split.ReadSlot("v0") == ((new BigInteger(0x5A5A5A5A5A5A5A5AUL) << 64) | new BigInteger(0xA5A5A5A5A5A5A5A5UL)), "split load exposes scheduled second beat");
        Check(split.Reservation is null, "reservation starts before second beat and is not recreated after interference");
        Check(split.Events is [{ AtomicWidth: 64, Order: MemoryOrder.Acquire }, { AtomicWidth: 64, Order: MemoryOrder.Acquire }] && split.AppliedSchedule.Count == 1, "split load records two acquire beats");
        foreach (var faultOffset in new[] { 0, 15 })
        {
            var state = State(16);
            state.Memory.Remove(Address + (ulong)faultOffset);
            state.Reservation = new(Address + 0x100, 8);
            execution = MirInterpreter.Execute(loadIr, state);
            Check(execution.Outcome == "UnmodeledFaultStop" && state.ReadSlot("v0") == 31, "faulted pair load does not commit destination");
            Check(state.Reservation == (faultOffset == 0 ? new ExclusiveReservation(Address + 0x100, 8) : new(Address, 16)), "reservation begins after first beat validation");
            Check(state.Events.Count == (faultOffset == 0 ? 1 : 2), "load fault preserves completed beat history");
        }

        var probe = new MirBuilder(Architecture.X64, Origin, "fixture.write-probe");
        probe.WriteProbe(probe.Const(64, Address), 16);
        probe.Write("rax", probe.Const(64, 99UL));
        var probeIr = Finish(probe);
        foreach (var permission in new[] { "missing", "partial", "denied", "allowed" })
        {
            var state = State(16);
            state.Slots["rax"] = 17;
            for (var i = 0; i < (permission == "partial" ? 15 : permission == "missing" ? 0 : 16); i++)
                state.WritePermissions[Address + (ulong)i] = true;
            if (permission == "denied") state.WritePermissions[Address + 15] = false;
            execution = MirInterpreter.Execute(probeIr, state);
            var expected = permission == "allowed" ? "Normal" : permission == "denied" ? "UnmodeledFaultStop" : "UnmodeledEnvironmentStop";
            Check(execution.Outcome == expected && state.ReadSlot("rax") == (permission == "allowed" ? 99 : 17), "write probe requires complete explicit permission");
            Check(state.Accesses.Count == 0 && state.Memory.Values.All(value => value == 0xA5) && state.Events.Count == 1, "write probe never reads or modifies data");
        }

        foreach (var ir in new[] { storeIr, loadIr })
        {
            var opcode = ir == storeIr ? OpCode.StoreExclusive : OpCode.LoadExclusive;
            var good = ir.Operations.Single(op => op.Code == opcode).Memory!;
            foreach (var bad in new MemoryOperation?[] { null, good with { AtomicWidth = 0 }, good with { AtomicWidth = 32 },
                good with { ElementWidth = 24 }, good with { Order = (MemoryOrder)999 }, good with { NonTemporal = true },
                good with { Order = opcode == OpCode.LoadExclusive ? MemoryOrder.Release : MemoryOrder.Acquire } })
                Check(MirValidator.Validate(Replace(ir, opcode, op => op with { Memory = bad })).Count > 0, "reject malformed exclusive atomic metadata");
            Check(MirValidator.Validate(Replace(ir, opcode, op => op with { WorldOut = op.WorldIn })).Count > 0, "exclusive World chain is required");
            Check(MirValidator.Validate(Replace(ir, opcode, op => op with { Fault = FaultPolicy.None })).Count > 0, "exclusive fault edge is required");
            Check(MirValidator.Validate(ir with { Architecture = Architecture.X64 }).Count > 0, "exclusive primitive is ARM only");
        }
        var plain = new MirBuilder(Architecture.Arm64, Origin, "fixture.ordered-load");
        plain.Load(plain.Const(64, Address), 64, new(MemoryOrder.Acquire, 64, 64));
        var plainIr = Finish(plain);
        foreach (var memory in new[] { new MemoryOperation(MemoryOrder.Acquire, 64, 32), new(MemoryOrder.Release, 64, 64), new(MemoryOrder.Acquire, 128, 64), new(MemoryOrder.Relaxed, 64, 256) })
            Check(MirValidator.Validate(Replace(plainIr, OpCode.Load, op => op with { Memory = memory })).Count > 0, "reject incompatible ordered memory metadata");
        Check(MirValidator.Validate(Replace(plainIr, OpCode.Constant, op => op with { Memory = new(MemoryOrder.Relaxed, 64, 64) })).Count > 0, "memory metadata belongs only on memory operations");
        Check(MirValidator.Validate(Replace(probeIr, OpCode.WriteProbe, op => op with { Immediate = 0 })).Count > 0, "zero-size permission probe is invalid");
        Check(MirValidator.Validate(Replace(probeIr, OpCode.WriteProbe, op => op with { Immediate = 4097 })).Count > 0, "oversized permission probe is invalid");

        var ordering = new MirBuilder(Architecture.Arm64, Origin, "fixture.ordering-events");
        ordering.CodeGuarded(ordering.Const(64, Origin.Address));
        var barrier = new BarrierOperation(BarrierKind.Dmb, BarrierDomain.InnerShareable, BarrierAccess.All, 11);
        ordering.Barrier(barrier);
        ordering.ClearExclusive();
        ordering.Prefetch(ordering.Const(64, 0xDEADBEEFUL), 31);
        ordering.Write("x0", ordering.Const(64, 99UL));
        var orderingIr = Finish(ordering);
        var orderedState = State(1);
        orderedState.Reservation = new(Address, 1);
        orderedState.Schedule.Enqueue(new(0, Address, [0xFE], false));
        execution = MirInterpreter.Execute(orderingIr, orderedState);
        Check(execution.Outcome == "Normal" && orderedState.ReadSlot("x0") == 99, "ordering effects continue without mapped prefetch data");
        Check(orderedState.Events is [{ Sequence: 0, Kind: "Barrier" }, { Sequence: 1, Kind: "ClearExclusive" }, { Sequence: 2, Kind: "Prefetch", Option: 31 }], "code-page lookup does not shift memory event numbering");
        Check(orderedState.Memory[Address] == 0xFE && orderedState.AppliedSchedule.Count == 1 && orderedState.Reservation is null, "scheduled effect precedes barrier and clear remains explicit");
        Check(orderedState.Accesses.Count == 0 && orderedState.Events[0].Barrier == barrier, "barrier and prefetch retain metadata without data accesses");
        foreach (var bad in new BarrierOperation?[] { null, barrier with { Kind = BarrierKind.Mfence }, barrier with { Domain = BarrierDomain.FullSystem },
            barrier with { Access = BarrierAccess.Loads }, barrier with { Option = 0 }, barrier with { Option = 16 } })
            Check(MirValidator.Validate(Replace(orderingIr, OpCode.Barrier, op => op with { Barrier = bad })).Count > 0, "reject barrier kind/domain/access/option mismatch");
        foreach (var code in new[] { OpCode.Barrier, OpCode.ClearExclusive, OpCode.Prefetch })
        {
            Check(MirValidator.Validate(Replace(orderingIr, code, op => op with { Fault = FaultPolicy.StopUnmodeled })).Count > 0, "nonfaulting ordering event rejects fault edge");
            Check(MirValidator.Validate(Replace(orderingIr, code, op => op with { WorldOut = op.WorldIn })).Count > 0, "ordering event requires World progression");
        }
        Check(MirValidator.Validate(Replace(orderingIr, OpCode.Prefetch, op => op with { Immediate = 32 })).Count > 0, "reject out-of-range prefetch hint");
        Check(MirValidator.Validate(Replace(orderingIr, OpCode.CodeGuarded, op => op with { Barrier = barrier })).Count > 0, "barrier metadata belongs only on barrier operations");

        foreach (var isLoad in new[] { false, true })
        {
            var conditional = new MirBuilder(Architecture.Arm64, Origin, "fixture.conditional-memory");
            var condition = conditional.Read("c", 1);
            var target = conditional.Read("x2", 64);
            if (isLoad) conditional.Write("x0", conditional.LoadIf(condition, target, 64));
            else conditional.StoreIf(condition, target, conditional.Const(64, 0x1122334455667788UL));
            conditional.Write("x1", conditional.Const(64, 99UL));
            var conditionalIr = Finish(conditional);
            var code = isLoad ? OpCode.LoadIf : OpCode.StoreIf;
            foreach (var mapped in new[] { false, true })
            {
                var inactive = State(8);
                inactive.Slots["c"] = 0;
                inactive.Slots["x2"] = mapped ? Address : Address + 0x1000;
                inactive.Reservation = new(Address, 8);
                inactive.Schedule.Enqueue(new(0, Address, [0xFE], true));
                execution = MirInterpreter.Execute(conditionalIr, inactive);
                Check(execution.Outcome == "Normal" && inactive.ReadSlot("x0") == (isLoad ? 0 : 17) && inactive.ReadSlot("x1") == 99, "inactive load yields zero and inactive store continues");
                Check(inactive.Accesses.Count == 0 && inactive.Events.Count == 0 && inactive.Memory.Values.All(value => value == 0xA5), "inactive memory operation has no access or event");
                Check(inactive.Reservation == new ExclusiveReservation(Address, 8) && inactive.Schedule.Count == 1 && inactive.AppliedSchedule.Count == 0, "inactive operation preserves reservation and pending schedule");
            }
            foreach (var fault in new[] { false, true })
            {
                var active = State(8);
                active.Slots["c"] = 1;
                active.Slots["x2"] = Address;
                active.Reservation = new(Address, 8);
                if (fault) active.Memory.Remove(Address + 7);
                execution = MirInterpreter.Execute(conditionalIr, active);
                Check(execution.Outcome == (fault ? "UnmodeledFaultStop" : "Normal") && active.ReadSlot("x1") == (fault ? 23 : 99), "active conditional fault stops subsequent commits");
                Check(active.ReadSlot("x0") == (isLoad && !fault ? new BigInteger(0xA5A5A5A5A5A5A5A5UL) : 17), "active load commits only after full access");
                Check(active.Events.Count == 1 && active.Events[0].Kind == code.ToString() && active.Events[0].SizeBytes == 8 && active.Events[0].AtomicWidth == 0 && active.Accesses.Count == 1, "active conditional access emits one ordinary memory event");
                Check(fault || isLoad ? active.Memory.Values.All(value => value == 0xA5) : Read(active, 8) == 0x1122334455667788UL, "conditional store validates complete range before writing");
                Check(active.Reservation == (!fault && !isLoad ? null : new ExclusiveReservation(Address, 8)), "successful conditional store invalidates overlapping reservation");
            }
            foreach (var mutation in new Func<Operation, Operation>[] {
                op => op with { Memory = new(MemoryOrder.Relaxed, 64, 64) },
                op => op with { Immediate = 1 }, op => op with { Slot = "x0" }, op => op with { Detail = "stray" },
                op => op with { WorldIn = -1 }, op => op with { WorldOut = op.WorldIn }, op => op with { Fault = FaultPolicy.None },
                op => op with { Barrier = barrier }, op => op with { Floating = new(FloatKind.Add, 64, 64) } })
                Check(MirValidator.Validate(Replace(conditionalIr, code, mutation)).Count > 0, "conditional memory rejects atomic metadata, stray fields and broken effects");
            foreach (var malformed in new[] { "condition", "address", "width" })
            {
                var invalid = new MirBuilder(Architecture.Arm64, Origin, "fixture.invalid-conditional-memory");
                var test = invalid.Const(malformed == "condition" ? 2 : 1, 1UL);
                var location = invalid.Const(malformed == "address" ? 32 : 64, Address);
                var width = malformed == "width" ? 7 : 64;
                if (isLoad) invalid.LoadIf(test, location, width);
                else invalid.StoreIf(test, location, invalid.Const(width, 0UL));
                Check(MirValidator.Validate(invalid.Finish(MirExit.Next(0x1004))).Count > 0, "conditional memory requires bool, address64 and whole bytes");
            }
        }
        var delayed = new MirBuilder(Architecture.Arm64, Origin, "fixture.conditional-schedule");
        delayed.LoadIf(delayed.Const(1, 0UL), delayed.Const(64, ulong.MaxValue), 64);
        delayed.StoreIf(delayed.Const(1, 0UL), delayed.Const(64, ulong.MaxValue), delayed.Const(64, 0UL));
        delayed.Write("x0", delayed.LoadIf(delayed.Const(1, 1UL), delayed.Const(64, Address), 64));
        var delayedIr = Finish(delayed);
        var delayedState = State(8);
        delayedState.Reservation = new(Address, 8);
        delayedState.Schedule.Enqueue(new(0, Address, [0xFE], false));
        execution = MirInterpreter.Execute(delayedIr, delayedState);
        Check(execution.Outcome == "Normal" && delayedState.ReadSlot("x0") == new BigInteger(0xA5A5A5A5A5A5A5FEUL), "first active conditional access sees event-zero scheduled write");
        Check(delayedState.Events is [{ Sequence: 0, Kind: "LoadIf" }] && delayedState.AppliedSchedule.Count == 1 && delayedState.Schedule.Count == 0 && delayedState.Reservation is null, "inactive effects do not consume or renumber scheduled memory events");
        return checks;
    }

    private static MirInstruction Replace(MirInstruction ir, OpCode code, Func<Operation, Operation> replacement) =>
        ir with { Operations = ir.Operations.Select(op => op.Code == code ? replacement(op) : op).ToArray() };

    private static MachineState State(int bytes)
    {
        var state = CoreChecks.CreateArmState();
        state.Slots["x0"] = 17;
        state.Slots["x1"] = 23;
        state.Slots["v0"] = 31;
        for (var i = 0; i < bytes; i++) state.Memory[Address + (ulong)i] = 0xA5;
        return state;
    }

    private static BigInteger Read(MachineState state, int bytes)
    {
        BigInteger result = 0;
        for (var i = 0; i < bytes; i++) result |= new BigInteger(state.Memory[Address + (ulong)i]) << (8 * i);
        return result;
    }
}
