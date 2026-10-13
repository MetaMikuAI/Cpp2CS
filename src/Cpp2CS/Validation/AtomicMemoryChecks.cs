using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Validation;

public static class AtomicMemoryChecks
{
    private const ulong Address = 0x8000;
    private static readonly InstructionOrigin Origin = new("fixture:atomic-memory", 0x1000, 0, new byte[] { 0x90 });

    public static int Run()
    {
        int checks = 0;
        void Check(bool result, string description) { CoreChecks.Require(result, description); checks++; }
        MirInstruction Program(int width, ulong address = Address)
        {
            var b = new MirBuilder(Architecture.X64, Origin, "fixture.atomic");
            Value old = b.AtomicRmw(b.Const(64, address), b.Const(width, 0x1234), b.Const(width, 0xA5), AtomicKind.CompareExchange);
            b.Write("rax", width > 64 ? b.Trunc(old, 64) : b.Zext(old, 64));
            return MirJson.Deserialize(MirJson.Serialize(b.Finish(MirExit.Next(0x1001))));
        }
        foreach (int width in new[] { 8, 16, 32, 64, 128 })
        {
            var ir = Program(width);
            Check(MirValidator.Validate(ir).Count == 0 && ir.Support == SupportClass.NormalPathOnly, "atomic IR validates and roundtrips with fault limitation");
            int bytes = width / 8;
            for (int index = 0; index < bytes; index++)
            foreach (string issue in new[] { "missing", "denied", "unknown" })
            {
                var state = State(bytes);
                state.Reservation = new(Address, bytes);
                if (issue == "missing") state.Memory.Remove(Address + (ulong)index);
                else if (issue == "denied") state.WritePermissions[Address + (ulong)index] = false;
                else state.WritePermissions.Remove(Address + (ulong)index);
                var result = MirInterpreter.Execute(ir, state);
                Check(result.Outcome == (issue == "unknown" ? "UnmodeledEnvironmentStop" : "UnmodeledFaultStop"), "atomic checks each byte mapping and explicit write permission");
                Check(state.Memory.Values.All(value => value == 0xA5) && state.ReadSlot("rax") == 19, "faulted atomic has no partial memory/register commit");
                Check(state.Reservation == new ExclusiveReservation(Address, bytes), "faulted atomic preserves reservation");
                Check(state.Events.Count == 1 && state.Events[0].PreviousData is null && state.Events[0].Data is null, "faulted atomic retains one boundary without an observed value");
            }
            foreach (bool success in new[] { false, true })
            {
                var state = State(bytes);
                if (success) for (int index = 1; index < bytes; index++) state.Memory[Address + (ulong)index] = 0;
                else state.Memory[Address] ^= 1;
                BigInteger old = Read(state, bytes);
                state.Reservation = new(Address, bytes);
                var result = MirInterpreter.Execute(ir, state);
                bool match = old == 0xA5;
                Check(result.Outcome == "Normal" && state.ReadSlot("rax") == (old & MirInterpreter.Mask(Math.Min(width, 64))), "CAS returns pre-event memory value");
                Check(Read(state, bytes) == (match ? new BigInteger(0x1234) & MirInterpreter.Mask(width) : old), "CAS commits desired or writes back unchanged old data");
                Check(state.Reservation is null && state.Events is [{ Kind: "AtomicRmw", Order: MemoryOrder.X64Locked }], "CAS failure is still a single writing event");
                Check(state.Events[0].Outcome == (match ? "Exchanged" : "CompareFailed") && state.Events[0].AtomicWidth == width, "CAS records compare result and full atomic width");
            }
        }

        foreach (ulong address in new[] { 0x0000800000000000UL, 0xFFFF7FFFFFFFFFF8UL, ulong.MaxValue - 3, Address + 1 })
        {
            var state = State(16, address);
            var result = MirInterpreter.Execute(Program(128, address), state);
            Check(result.Outcome == "UnmodeledFaultStop" && state.ReadSlot("rax") == 19 && state.Memory.Values.All(value => value == 0xA5), "direct atomic IR rejects noncanonical, wrapping, unaligned 128-bit addresses");
        }

        foreach (int boundary in new[] { 0, 1 })
        {
            var state = State(8);
            state.Schedule.Enqueue(new(boundary, Address, new byte[8], false));
            var result = MirInterpreter.Execute(Program(64), state);
            Check(result.Outcome == "Normal" && state.Events.Count == 1 && state.AppliedSchedule.Count == 1 - boundary && state.Schedule.Count == boundary, "external write can occur before atomic event or remain after it, never inside it");
            Check(state.ReadSlot("rax") == (boundary == 0 ? 0 : new BigInteger(0xA5A5A5A5A5A5A5A5UL)), "atomic reads the single event pre-state");
        }

        var reference = Program(64);
        int atomicIndex = reference.Operations.ToList().FindIndex(op => op.Code == OpCode.AtomicRmw);
        Operation atomic = reference.Operations[atomicIndex];
        foreach (Operation invalid in new[]
        {
            atomic with { Atomic = null },
            atomic with { Atomic = new((AtomicKind)999) },
            atomic with { Atomic = new(AtomicKind.Add, MemoryOrder.Relaxed) },
            atomic with { Memory = new(MemoryOrder.Relaxed, 64, 64) },
            atomic with { Barrier = new(BarrierKind.Mfence, BarrierDomain.FullSystem, BarrierAccess.All, 0) },
            atomic with { Fault = FaultPolicy.None },
            atomic with { WorldOut = atomic.WorldOut + 1 },
            atomic with { Inputs = atomic.Inputs[..2] },
            atomic with { Immediate = 1 },
            atomic with { Slot = "rax" },
            atomic with { Detail = "invalid" }
        })
        {
            Operation[] operations = reference.Operations.ToArray();
            operations[atomicIndex] = invalid;
            Check(MirValidator.Validate(reference with { Operations = operations }).Count != 0, "atomic validator rejects malformed contract");
        }
        var wrongArchitecture = reference with { Architecture = Architecture.Arm64 };
        Check(MirValidator.Validate(wrongArchitecture).Count != 0, "atomic x64 ordering is architecture scoped");
        var wide = Program(128);
        Operation[] wideOperations = wide.Operations.ToArray();
        int wideIndex = Array.FindIndex(wideOperations, op => op.Code == OpCode.AtomicRmw);
        wideOperations[wideIndex] = wideOperations[wideIndex] with { Atomic = new(AtomicKind.Add) };
        Check(MirValidator.Validate(wide with { Operations = wideOperations }).Count != 0, "128-bit atomic primitive is restricted to CMPXCHG16B");

        var store = new MirBuilder(Architecture.X64, Origin, "fixture.denied-store");
        store.Store(store.Const(64, Address), store.Const(64, 0));
        store.Write("rax", store.Const(64, 99));
        var deniedStore = State(8);
        deniedStore.WritePermissions[Address + 7] = false;
        var execution = MirInterpreter.Execute(store.Finish(MirExit.Next(0x1001)), deniedStore);
        Check(execution.Outcome == "UnmodeledFaultStop" && Read(deniedStore, 8) == new BigInteger(0xA5A5A5A5A5A5A5A5UL) && deniedStore.ReadSlot("rax") == 19,
            "ordinary Store respects explicit denied permission before byte commits");
        return checks;
    }

    private static MachineState State(int bytes, ulong address = Address)
    {
        var state = new MachineState();
        state.Slots["rax"] = 19;
        for (int index = 0; index < bytes; index++)
        {
            state.Memory[unchecked(address + (ulong)index)] = 0xA5;
            state.WritePermissions[unchecked(address + (ulong)index)] = true;
        }
        return state;
    }

    private static BigInteger Read(MachineState state, int bytes)
    {
        BigInteger value = 0;
        for (int index = 0; index < bytes; index++) value |= new BigInteger(state.Memory[Address + (ulong)index]) << (index * 8);
        return value;
    }
}
