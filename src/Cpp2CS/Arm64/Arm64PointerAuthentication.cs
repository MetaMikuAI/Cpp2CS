using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private static LiftResult PointerAuthentication(Context c)
    {
        var selector = c.Field(5, 7);
        var keyB = (selector & 2) != 0;
        var authenticate = (selector & 4) != 0;
        var use1716 = (selector & 0x18) == 8;
        var register = use1716 ? 17 : 30;
        var modifier = use1716 ? c.Read(16, 64) : (selector & 1) != 0 ? c.Read(31, 64, true) : c.C(64, 0);
        var pointer = c.Read(register, 64);
        var enabled = c.B.Read(keyB ? "pauth_ib_enabled" : "pauth_ia_enabled", 1);
        var key = c.B.Read(keyB ? "apib_key" : "apia_key", 128);
        var low = c.B.And(pointer, c.C(64, 0x0000FFFFFFFFFFFF));
        var sign = c.B.Extract(pointer, authenticate ? 55 : 63, 1);
        var extension = c.B.Shl(c.B.Sext(sign, 64), c.C(64, 48));
        var original = c.B.Or(low, extension);
        var pac = c.B.Qarma5(original, modifier, key);
        const ulong pacMask = 0xFF7F000000000000;
        Value result;
        if (authenticate)
        {
            var matches = c.B.Eq(c.B.And(pointer, c.C(64, pacMask)), c.B.And(pac, c.C(64, pacMask)));
            var poison = c.B.Or(c.B.And(original, c.C(64, ~(3UL << 61))), c.C(64, (keyB ? 2UL : 1UL) << 61));
            result = c.B.Select(matches, original, poison);
        }
        else
        {
            var high = c.B.Extract(pointer, 48, 16);
            var canonical = c.B.Or(c.B.Eq(high, c.C(16, 0)), c.B.Eq(high, c.C(16, 0xFFFF)));
            pac = c.B.Select(canonical, pac, c.B.Xor(pac, c.C(64, 1UL << 62)));
            result = c.B.Or(c.B.Or(low, c.B.And(pac, c.C(64, pacMask))), c.B.Shl(c.B.Zext(sign, 64), c.C(64, 55)));
        }
        c.Write(register, c.B.Select(enabled, result, pointer));
        return c.Done();
    }
}
