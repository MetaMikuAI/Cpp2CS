using System.Numerics;

namespace Cpp2CS.Ir;

internal static partial class MemoryEffects
{
    public static MemoryEffectResult Atomic(Operation op, MachineState state, ulong address, BigInteger operand, BigInteger expected)
    {
        BeforeEvent(state);
        int width = op.Result!.Value.Width, bytes = width / 8;
        ulong end = unchecked(address + (ulong)bytes - 1);
        bool addressFault = end < address || ((long)address << 16 >> 16) != (long)address ||
            ((long)end << 16 >> 16) != (long)end || width == 128 && (address & 15) != 0;
        bool missing = false, denied = false, unknown = false;
        for (int i = 0; i < bytes; i++)
        {
            ulong location = unchecked(address + (ulong)i);
            missing |= !state.Memory.ContainsKey(location);
            if (!state.WritePermissions.TryGetValue(location, out bool allowed)) unknown = true;
            else denied |= !allowed;
        }
        state.Accesses.Add($"AtomicRmw:0x{address:X}:{bytes}");
        string? stop = addressFault || missing || denied ? "UnmodeledFaultStop" : unknown ? "UnmodeledEnvironmentStop" : null;
        if (stop is not null)
        {
            state.Events.Add(new(state.Events.Count, "AtomicRmw", address, bytes, width,
                MemoryOrder.X64Locked, stop, Atomic: op.Atomic));
            return new(Outcome: stop, Reason: addressFault || missing || denied ? "atomic read/write access" : "atomic write permissions are required");
        }
        BigInteger old = 0;
        for (int i = 0; i < bytes; i++) old |= new BigInteger(state.Memory[unchecked(address + (ulong)i)]) << (8 * i);
        BigInteger next = op.Atomic!.Kind switch
        {
            AtomicKind.Exchange => operand,
            AtomicKind.Add => old + operand,
            AtomicKind.Sub => old - operand,
            AtomicKind.And => old & operand,
            AtomicKind.Or => old | operand,
            AtomicKind.Xor => old ^ operand,
            AtomicKind.Neg => -old,
            AtomicKind.Not => ~old,
            AtomicKind.CompareExchange => old == expected ? operand : old,
            _ => throw new InvalidOperationException("Unknown atomic operation")
        };
        next &= MirInterpreter.Mask(width);
        for (int i = 0; i < bytes; i++) state.Memory[unchecked(address + (ulong)i)] = (byte)((next >> (8 * i)) & 255);
        InvalidateOverlapping(state, address, bytes);
        string outcome = op.Atomic.Kind == AtomicKind.CompareExchange ? old == expected ? "Exchanged" : "CompareFailed" : "Completed";
        state.Events.Add(new(state.Events.Count, "AtomicRmw", address, bytes, width,
            MemoryOrder.X64Locked, outcome, Data: "0x" + next.ToString("X"), Atomic: op.Atomic, PreviousData: "0x" + old.ToString("X")));
        return new(old);
    }
}
