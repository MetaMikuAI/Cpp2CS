using System.Numerics;

namespace Cpp2CS.Ir;

internal readonly record struct MemoryEffectResult(BigInteger Value = default, string? Outcome = null, string? Reason = null);

// Executes one concrete event schedule. Ordering metadata is retained, not a weak-memory solver.
internal static class MemoryEffects
{
    public static MemoryEffectResult Execute(Operation op, MachineState state, BigInteger addressBits, BigInteger data)
    {
        var address = (ulong)addressBits;
        if (op.Code is OpCode.Barrier or OpCode.ClearExclusive or OpCode.Prefetch)
        {
            BeforeEvent(state);
            if (op.Code == OpCode.ClearExclusive) state.Reservation = null;
            state.Events.Add(new(state.Events.Count, op.Code.ToString(), op.Code == OpCode.Prefetch ? address : null,
                0, 0, MemoryOrder.Relaxed, "Completed", (int)op.Immediate, Barrier: op.Barrier));
            return new();
        }
        if (op.Code == OpCode.WriteProbe)
        {
            BeforeEvent(state);
            var size = (int)op.Immediate;
            var unknown = false;
            var denied = false;
            for (var i = 0; i < size; i++)
            {
                if (!state.WritePermissions.TryGetValue(unchecked(address + (ulong)i), out var allowed)) unknown = true;
                else if (!allowed) denied = true;
            }
            var outcome = denied ? "UnmodeledFaultStop" : unknown ? "UnmodeledEnvironmentStop" : null;
            state.Events.Add(new(state.Events.Count, "WriteProbe", address, size, 0, MemoryOrder.Relaxed, outcome ?? "Completed"));
            return new(Outcome: outcome, Reason: outcome is null ? null : "write-access permission probe");
        }
        var load = op.Code is OpCode.Load or OpCode.LoadExclusive or OpCode.LoadIf;
        var width = load ? op.Result!.Value.Width : op.Inputs[op.Code == OpCode.StoreIf ? 2 : 1].Width;
        var bytes = width / 8;
        var spec = op.Memory;
        var beatBytes = spec is { AtomicWidth: > 0 } ? spec.AtomicWidth / 8 : bytes;
        BigInteger value = 0;
        for (var offset = 0; offset < bytes; offset += beatBytes)
        {
            BeforeEvent(state);
            var beatAddress = unchecked(address + (ulong)offset);
            if (op.Code == OpCode.StoreExclusive)
            {
                if (!state.ExclusiveStoreDecisions.TryDequeue(out var permitted))
                {
                    state.Events.Add(new(state.Events.Count, "StoreExclusive", address, bytes, width, spec!.Order,
                        "UnmodeledEnvironmentStop"));
                    return new(Outcome: "UnmodeledEnvironmentStop", Reason: "exclusive-store decision is required");
                }
                var match = state.Reservation is { } reservation && reservation.Address == address && reservation.SizeBytes == bytes;
                state.Reservation = null;
                if (!permitted || !match)
                {
                    state.Events.Add(new(state.Events.Count, "StoreExclusive", address, bytes, width, spec!.Order, "Failed"));
                    return new(1);
                }
            }
            state.Accesses.Add($"{(load ? "Load" : "Store")}:0x{beatAddress:X}:{beatBytes}");
            for (var i = 0; i < beatBytes; i++)
            {
                var location = unchecked(beatAddress + (ulong)i);
                if (!state.Memory.ContainsKey(location) || !load && state.WritePermissions.TryGetValue(location, out var writable) && !writable)
                {
                    state.Events.Add(new(state.Events.Count, op.Code.ToString(), beatAddress, beatBytes,
                        spec?.AtomicWidth ?? 0, spec?.Order ?? MemoryOrder.Relaxed, "UnmodeledFaultStop"));
                    return new(Outcome: "UnmodeledFaultStop", Reason: "memory access");
                }
            }
            if (op.Code == OpCode.LoadExclusive && offset == 0) state.Reservation = new(address, bytes);
            BigInteger beat = 0;
            for (var i = 0; i < beatBytes; i++)
            {
                if (load) beat |= new BigInteger(state.Memory[unchecked(beatAddress + (ulong)i)]) << (8 * i);
                else state.Memory[unchecked(beatAddress + (ulong)i)] = (byte)((data >> (8 * (offset + i))) & 255);
            }
            if (load) value |= beat << (8 * offset);
            else
            {
                beat = (data >> (8 * offset)) & MirInterpreter.Mask(beatBytes * 8);
                InvalidateOverlapping(state, beatAddress, beatBytes);
            }
            state.Events.Add(new(state.Events.Count, op.Code.ToString(), beatAddress, beatBytes,
                spec?.AtomicWidth ?? 0, spec?.Order ?? MemoryOrder.Relaxed, "Completed",
                Data: "0x" + beat.ToString("X"), NonTemporal: spec?.NonTemporal ?? false));
        }
        return new(load ? value : BigInteger.Zero);
    }

    private static void BeforeEvent(MachineState state)
    {
        while (state.Schedule.TryPeek(out var next) && next.BeforeEvent == state.Events.Count)
        {
            state.Schedule.Dequeue();
            state.AppliedSchedule.Add(next);
            if (next.Address is { } address)
            {
                for (var i = 0; i < next.Bytes.Length; i++)
                    if (!state.Memory.ContainsKey(unchecked(address + (ulong)i)))
                        throw new InvalidOperationException("Scheduled write is outside mapped memory");
                for (var i = 0; i < next.Bytes.Length; i++) state.Memory[unchecked(address + (ulong)i)] = next.Bytes[i];
                InvalidateOverlapping(state, address, next.Bytes.Length);
            }
            if (next.InvalidateExclusive) state.Reservation = null;
        }
    }

    private static void InvalidateOverlapping(MachineState state, ulong address, int size)
    {
        if (state.Reservation is not { } reservation) return;
        for (var i = 0; i < size; i++)
            if (unchecked(address + (ulong)i - reservation.Address) < (ulong)reservation.SizeBytes)
            {
                state.Reservation = null;
                return;
            }
    }
}
