using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private readonly record struct MemoryShape(int Width, int DestinationWidth, bool Load, bool Signed, bool Vector);

    private static bool SingleShape(Context c, out MemoryShape shape)
    {
        var size = c.Field(30, 2);
        var opcode = c.Field(22, 2);
        var vector = c.Bit(26);
        shape = default;
        if (vector)
        {
            if (opcode >= 2 && size != 0) return false;
            var width = opcode >= 2 ? 128 : 8 << size;
            shape = new(width, 128, (opcode & 1) != 0, false, true);
        }
        else
        {
            if ((opcode == 2 && size == 3) || (opcode == 3 && size >= 2)) return false;
            shape = new(8 << size, opcode == 2 || size == 3 ? 64 : 32, opcode != 0, opcode >= 2, false);
        }
        return true;
    }

    private static LiftResult SingleMemory(Context c, int form)
    {
        if (!SingleShape(c, out var shape)) return c.Reject("Reserved or prefetch load/store form");
        var mode = form == 1 ? c.Field(10, 2) : 0;
        if (form == 1 && mode == 2) return c.Reject("Unprivileged memory access is outside the current profile");
        var writeback = form == 1 && mode is 1 or 3;
        if (writeback && !shape.Vector && c.Rn == c.Rd && c.Rn != 31)
            return c.Reject("Constrained-unpredictable writeback overlap");
        var basis = c.Read(c.Rn, 64, true);
        Value offset;
        if (form == 0) offset = c.C(64, (ulong)c.Field(10, 12) * (ulong)(shape.Width / 8));
        else if (form == 1) offset = c.C(64, unchecked((ulong)SignExtend((ulong)c.Field(12, 9), 9)));
        else
        {
            var option = c.Field(13, 3);
            if ((option & 2) == 0) return c.Reject("Reserved memory register extension");
            var sourceWidth = (option & 1) != 0 ? 64 : 32;
            offset = c.Read(c.Rm, sourceWidth);
            if (sourceWidth == 32) offset = (option & 4) != 0 ? c.B.Sext(offset, 64) : c.B.Zext(offset, 64);
            if (c.Bit(12)) offset = c.B.Mul(offset, c.C(64, (ulong)(shape.Width / 8)));
        }
        var updated = c.B.Add(basis, offset);
        var address = mode == 1 ? basis : updated;
        if (shape.Load)
        {
            var value = c.B.Load(address, shape.Width);
            WriteLoaded(c, c.Rd, value, shape);
        }
        else
        {
            var value = shape.Vector ? c.ReadVector(c.Rd, shape.Width) : c.Read(c.Rd, shape.Width);
            c.B.Store(address, value);
        }
        if (writeback) c.Write(c.Rn, updated, true);
        return c.Done();
    }

    private static void WriteLoaded(Context c, int register, Value value, MemoryShape shape)
    {
        if (shape.Vector) c.WriteVector(register, value);
        else
        {
            if (value.Width != shape.DestinationWidth)
                value = shape.Signed ? c.B.Sext(value, shape.DestinationWidth) : c.B.Zext(value, shape.DestinationWidth);
            c.Write(register, value);
        }
    }

    private static LiftResult PairMemory(Context c)
    {
        var opcode = c.Field(30, 2);
        var vector = c.Bit(26);
        var load = c.Bit(22);
        var mode = c.Field(23, 2);
        if (opcode == 3 || (!vector && opcode == 1 && (!load || mode == 0))) return c.Reject("Reserved pair memory encoding");
        var width = vector ? 32 << opcode : (opcode == 2 ? 64 : 32);
        var destination = !vector && opcode == 1 ? 64 : width;
        var second = c.Field(10, 5);
        var writeback = mode is 1 or 3;
        if (load && c.Rd == second) return c.Reject("Constrained-unpredictable duplicate load destinations");
        if (writeback && !vector && c.Rn != 31 && (c.Rn == c.Rd || c.Rn == second))
            return c.Reject("Constrained-unpredictable pair writeback overlap");
        var shape = new MemoryShape(width, destination, load, !vector && opcode == 1, vector);
        var basis = c.Read(c.Rn, 64, true);
        var offset = SignExtend((ulong)c.Field(15, 7), 7) * (width / 8);
        var updated = c.B.Add(basis, c.C(64, unchecked((ulong)offset)));
        var address = mode == 1 ? basis : updated;
        var secondAddress = c.B.Add(address, c.C(64, (ulong)(width / 8)));
        if (load)
        {
            var firstValue = c.B.Load(address, width);
            var secondValue = c.B.Load(secondAddress, width);
            WriteLoaded(c, c.Rd, firstValue, shape);
            WriteLoaded(c, second, secondValue, shape);
        }
        else
        {
            var firstValue = vector ? c.ReadVector(c.Rd, width) : c.Read(c.Rd, width);
            var secondValue = vector ? c.ReadVector(second, width) : c.Read(second, width);
            c.B.Store(address, firstValue);
            c.B.Store(secondAddress, secondValue);
        }
        if (writeback) c.Write(c.Rn, updated, true);
        return c.Done();
    }

    private static LiftResult LiteralMemory(Context c)
    {
        var opcode = c.Field(30, 2);
        if (opcode == 3) return c.Reject("Prefetch or reserved literal encoding");
        var vector = c.Bit(26);
        var width = vector ? 32 << opcode : (opcode == 1 ? 64 : 32);
        var shape = new MemoryShape(width, !vector && opcode == 2 ? 64 : width, true, !vector && opcode == 2, vector);
        var address = c.Address(SignExtend((ulong)c.Field(5, 19), 19) << 2);
        WriteLoaded(c, c.Rd, c.B.Load(address, width), shape);
        return c.Done();
    }
}
