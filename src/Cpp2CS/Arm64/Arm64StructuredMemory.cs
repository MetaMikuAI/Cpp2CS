using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private static LiftResult StructureMultiple(Context c)
    {
        var writeback = c.Bit(23);
        if (c.Bit(21) || (!writeback && c.Rm != 0))
            return c.Reject("Reserved multiple-structure addressing bits");
        var (repeat, structures) = c.Field(12, 4) switch
        {
            0 => (1, 4),
            2 => (4, 1),
            4 => (1, 3),
            6 => (3, 1),
            7 => (1, 1),
            8 => (1, 2),
            10 => (2, 1),
            _ => (0, 0)
        };
        if (repeat == 0) return c.Reject("Reserved multiple-structure opcode");
        var width = c.Bit(30) ? 128 : 64;
        var elementWidth = 8 << c.Field(10, 2);
        if (width == 64 && elementWidth == 64 && structures != 1)
            return c.Reject("One D element is reserved for LD/ST2-4 multiple structures");
        var load = c.Bit(22);
        var basis = c.Read(c.Rn, 64, true);
        var bytes = repeat * structures * width / 8;
        var increment = StructureIncrement(c, bytes);
        var values = new Value[repeat * structures];
        for (var register = 0; register < values.Length; register++)
            values[register] = c.ReadVector((c.Rd + register) & 31, width);
        var offset = 0;
        // LD/ST1 advances by register; LD/ST2-4 interleave matching elements.
        for (var r = 0; r < repeat; r++)
        for (var lane = 0; lane < width / elementWidth; lane++)
        for (var structure = 0; structure < structures; structure++)
        {
            var register = r + structure;
            var address = c.B.Add(basis, c.C(64, (ulong)offset));
            if (load)
            {
                var element = c.B.Load(address, elementWidth);
                values[register] = Insert(c, values[register], element, lane * elementWidth);
                c.WriteVector((c.Rd + register) & 31, values[register]);
            }
            else
                c.B.Store(address, c.B.Extract(values[register], lane * elementWidth, elementWidth));
            offset += elementWidth / 8;
        }
        if (writeback) c.Write(c.Rn, c.B.Add(basis, increment), true);
        return c.Done();
    }

    private static LiftResult StructureSingle(Context c)
    {
        var writeback = c.Bit(23);
        if (!writeback && c.Rm != 0) return c.Reject("Reserved single-structure addressing bits");
        var opcode = c.Field(13, 3);
        var size = c.Field(10, 2);
        var s = c.Field(12, 1);
        var q = c.Field(30, 1);
        var scale = opcode >> 1;
        var structures = ((opcode & 1) << 1) + c.Field(21, 1) + 1;
        var load = c.Bit(22);
        var replicate = scale == 3;
        var index = 0;
        switch (scale)
        {
            case 0: index = (q << 3) | (s << 2) | size; break;
            case 1:
                if ((size & 1) != 0) return c.Reject("Reserved H lane size");
                index = (q << 2) | (s << 1) | (size >> 1);
                break;
            case 2:
                if ((size & 2) != 0 || (size == 1 && s != 0))
                    return c.Reject("Reserved S/D lane selector");
                index = size == 0 ? (q << 1) | s : q;
                if (size == 1) scale = 3;
                break;
            case 3:
                if (!load || s != 0) return c.Reject("Reserved replicate load encoding");
                scale = size;
                break;
        }
        var elementWidth = 8 << scale;
        var width = 64 << q;
        var basis = c.Read(c.Rn, 64, true);
        var increment = StructureIncrement(c, structures * elementWidth / 8);
        for (var structure = 0; structure < structures; structure++)
        {
            var register = (c.Rd + structure) & 31;
            var address = c.B.Add(basis, c.C(64, (ulong)(structure * elementWidth / 8)));
            if (load)
            {
                var element = c.B.Load(address, elementWidth);
                var value = replicate ? Replicate(c, element, width)
                    : Insert(c, c.ReadVector(register, 128), element, index * elementWidth);
                c.WriteVector(register, value);
            }
            else
                c.B.Store(address, c.B.Extract(c.ReadVector(register, 128), index * elementWidth, elementWidth));
        }
        if (writeback) c.Write(c.Rn, c.B.Add(basis, increment), true);
        return c.Done();
    }

    private static Value StructureIncrement(Context c, int bytes) => c.Bit(23) && c.Rm != 31
        ? c.Read(c.Rm, 64) : c.C(64, (ulong)bytes);
}
