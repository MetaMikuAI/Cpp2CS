using Cpp2CS.Ir;
using System.Numerics;

namespace Cpp2CS.Validation;

public static class DivisionChecks
{
    public static int Run()
    {
        var checks = 0;
        foreach (var signed in new[] { false, true })
        {
            var ir = Fixture(8, signed);
            var state = new MachineState();
            for (var dividend = 0; dividend < 256; dividend++)
            for (var divisor = 0; divisor < 256; divisor++)
            {
                state.Slots["x0"] = dividend;
                state.Slots["x1"] = divisor;
                MirInterpreter.Execute(ir, state);
                var a = signed && dividend >= 128 ? dividend - 256 : dividend;
                var b = signed && divisor >= 128 ? divisor - 256 : divisor;
                var quotient = MagnitudeQuotient(Math.Abs(a), Math.Abs(b));
                if ((a < 0) != (b < 0)) quotient = -quotient;
                CoreChecks.Require(state.ReadSlot("x2") == (quotient & 255), "8-bit total division");
                checks++;
            }
        }
        (ulong A, ulong B, ulong Unsigned, ulong Signed)[] cases =
        [
            (0, 0, 0, 0),
            (ulong.MaxValue, 0, 0, 0),
            (1UL << 63, ulong.MaxValue, 0, 1UL << 63),
            (ulong.MaxValue, 2, 0x7FFFFFFFFFFFFFFF, 0),
            (0xFFFFFFFFFFFFFFF9, 3, 0x5555555555555553, 0xFFFFFFFFFFFFFFFE),
            (7, 0xFFFFFFFFFFFFFFFD, 0, 0xFFFFFFFFFFFFFFFE),
            (1UL << 63, 2, 1UL << 62, 0xC000000000000000),
            (ulong.MaxValue, ulong.MaxValue, 1, 1)
        ];
        foreach (var signed in new[] { false, true })
        {
            var ir = Fixture(64, signed);
            foreach (var item in cases)
            {
                var state = new MachineState();
                state.Slots["x0"] = item.A;
                state.Slots["x1"] = item.B;
                MirInterpreter.Execute(ir, state);
                CoreChecks.Require(state.ReadSlot("x2") == new BigInteger(signed ? item.Signed : item.Unsigned), "64-bit division boundary");
                checks++;
            }
        }
        var invalid = new MirBuilder(Architecture.Arm64, new("fixture:division", 0x1000, 0, new byte[4]), "fixture.division-width");
        invalid.UDiv(invalid.Const(32, 1UL), invalid.Const(64, 2UL));
        CoreChecks.Require(MirValidator.Validate(invalid.Finish(MirExit.Next(0x1004))).Count != 0, "division requires equal widths");
        return checks + 1;
    }

    private static MirInstruction Fixture(int width, bool signed)
    {
        var b = new MirBuilder(Architecture.Arm64, new("fixture:division", 0x1000, 0, new byte[4]), "fixture.total-division");
        var dividend = b.Trunc(b.Read("x0", 64), width);
        var divisor = b.Trunc(b.Read("x1", 64), width);
        var quotient = signed ? b.SDiv(dividend, divisor) : b.UDiv(dividend, divisor);
        b.Write("x2", b.Zext(quotient, 64));
        return MirJson.Deserialize(MirJson.Serialize(b.Finish(MirExit.Next(0x1004))));
    }

    private static int MagnitudeQuotient(int dividend, int divisor)
    {
        if (divisor == 0) return 0;
        var quotient = 0;
        while (dividend >= divisor) { dividend -= divisor; quotient++; }
        return quotient;
    }
}
