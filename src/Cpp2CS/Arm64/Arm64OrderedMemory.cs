using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private static LiftResult OrderedMemory(Context c)
    {
        var elementWidth = 8 << c.Field(30, 2);
        var ordered = c.Bit(23);
        var load = c.Bit(22);
        var pair = c.Bit(21);
        var status = c.Field(16, 5);
        var acqrel = c.Bit(15);
        var second = c.Field(10, 5);
        if (ordered && (pair || status != 31 || second != 31 || !acqrel))
            return c.Reject("Reserved, limited-order, or LSE memory form");
        if (!ordered && (pair ? elementWidth < 32 : second != 31))
            return c.Reject("Reserved or LSE exclusive memory form");
        if (!ordered && load && status != 31)
            return c.Reject("Reserved exclusive-load status field");
        if (load && pair && c.Rd == second)
            return c.Reject("Constrained-unpredictable duplicate exclusive-load destinations");
        if (!ordered && !load && (status == c.Rd || pair && status == second || status == c.Rn && c.Rn != 31))
            return c.Reject("Constrained-unpredictable exclusive-store status overlap");

        var width = pair ? elementWidth * 2 : elementWidth;
        var address = c.Read(c.Rn, 64, true);
        c.B.Guard(c.B.Eq(c.B.And(address, c.C(64, (ulong)(width / 8 - 1))), c.C(64, 0)),
            "ordered/exclusive access alignment fault is an explicit unmodeled stop");
        var order = !acqrel ? MemoryOrder.Relaxed : load ? MemoryOrder.Acquire : MemoryOrder.Release;
        var memory = new MemoryOperation(order, elementWidth, load && width == 128 ? 64 : width);
        if (load)
        {
            var data = ordered ? c.B.Load(address, width, memory) : c.B.LoadExclusive(address, width, memory);
            c.Write(c.Rd, pair ? c.B.Extract(data, 0, elementWidth) : data);
            if (pair) c.Write(second, c.B.Extract(data, elementWidth, elementWidth));
        }
        else
        {
            var data = c.Read(c.Rd, elementWidth);
            if (pair) data = c.B.Concat(c.Read(second, elementWidth), data);
            if (ordered) c.B.Store(address, data, memory);
            else c.Write(status, c.B.StoreExclusive(address, data, memory));
        }
        return c.Done();
    }

    private static LiftResult MemoryBarrier(Context c)
    {
        var opcode = c.Field(5, 3);
        var option = c.Field(8, 4);
        if (opcode == 2)
        {
            c.B.ClearExclusive();
            return c.Done();
        }
        if (opcode == 6)
        {
            if (option != 15) return c.Reject("Reserved ISB option");
            c.B.Barrier(new(BarrierKind.Isb, BarrierDomain.FullSystem, BarrierAccess.All, option));
            return c.Done();
        }
        if ((option & 3) == 0)
            return c.Reject("Reserved barrier option or unsupported SSBB/PSSBB alias");
        var kind = opcode == 4 ? BarrierKind.Dsb : BarrierKind.Dmb;
        var domain = (option >> 2) switch
        {
            0 => BarrierDomain.OuterShareable,
            1 => BarrierDomain.NonShareable,
            2 => BarrierDomain.InnerShareable,
            _ => BarrierDomain.FullSystem
        };
        var access = (option & 3) switch
        {
            1 => BarrierAccess.Loads,
            2 => BarrierAccess.Stores,
            _ => BarrierAccess.All
        };
        c.B.Barrier(new(kind, domain, access, option));
        return c.Done();
    }
}
