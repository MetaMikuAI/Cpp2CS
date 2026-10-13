using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private static LiftResult Prefetch(Context c, int form)
    {
        Value address;
        if (form == 3)
            address = c.Address(SignExtend((ulong)c.Field(5, 19), 19) << 2);
        else
        {
            var basis = c.Read(c.Rn, 64, true);
            Value offset;
            if (form == 0) offset = c.C(64, (ulong)c.Field(10, 12) << 3);
            else if (form == 1) offset = c.C(64, unchecked((ulong)SignExtend((ulong)c.Field(12, 9), 9)));
            else
            {
                var option = c.Field(13, 3);
                if ((option & 2) == 0) return c.Reject("Reserved prefetch register extension");
                var sourceWidth = (option & 1) != 0 ? 64 : 32;
                offset = c.Read(c.Rm, sourceWidth);
                if (sourceWidth == 32) offset = (option & 4) != 0 ? c.B.Sext(offset, 64) : c.B.Zext(offset, 64);
                if (c.Bit(12)) offset = c.B.Shl(offset, c.C(64, 3));
            }
            address = c.B.Add(basis, offset);
        }
        c.B.Prefetch(address, c.Rd);
        return c.Done();
    }
}
