using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private static LiftResult ConditionalSelect(Context c)
    {
        var condition = c.Condition(c.Field(12, 4));
        var left = c.Read(c.Rn, c.Width);
        var right = c.Read(c.Rm, c.Width);
        if (c.Bit(30)) right = c.B.Not(right);
        if (c.Bit(10)) right = c.B.Add(right, c.C(c.Width, 1));
        c.Write(c.Rd, c.B.Select(condition, left, right));
        return c.Done();
    }

    private static LiftResult ConditionalCompare(Context c)
    {
        var condition = c.Condition(c.Field(12, 4));
        var left = c.Read(c.Rn, c.Width);
        var right = c.Bit(11) ? c.C(c.Width, (ulong)c.Field(16, 5)) : c.Read(c.Rm, c.Width);
        var subtract = c.Bit(30);
        var sum = Arithmetic.AddWithCarry(c.B, left, subtract ? c.B.Not(right) : right, c.C(1, subtract ? 1UL : 0UL));
        var values = new[] { c.B.Extract(sum.Result, c.Width - 1, 1), c.B.Eq(sum.Result, c.C(c.Width, 0)), sum.Carry, sum.Overflow };
        var slots = new[] { "n", "z", "c", "v" };
        for (var i = 0; i < 4; i++) c.B.Write(slots[i], c.B.Select(condition, values[i], c.C(1, (ulong)c.Field(3 - i, 1))));
        return c.Done();
    }

    private static LiftResult VariableShift(Context c)
    {
        var opcode = c.Field(10, 6);
        if (opcode is 2 or 3)
        {
            var dividend = c.Read(c.Rn, c.Width);
            var divisor = c.Read(c.Rm, c.Width);
            c.Write(c.Rd, opcode == 2 ? c.B.UDiv(dividend, divisor) : c.B.SDiv(dividend, divisor));
            return c.Done();
        }
        if (opcode is < 8 or > 11) return c.Reject("CRC and other two-source operations are not implemented");
        var value = c.Read(c.Rn, c.Width);
        var amount = c.B.And(c.Read(c.Rm, c.Width), c.C(c.Width, (ulong)(c.Width - 1)));
        Value result = opcode switch
        {
            8 => c.B.Shl(value, amount),
            9 => c.B.Shr(value, amount),
            10 => c.B.Sar(value, amount),
            11 => c.B.Or(c.B.Shr(value, amount), c.B.Shl(value, c.B.And(c.B.Sub(c.C(c.Width, 0), amount), c.C(c.Width, (ulong)(c.Width - 1))))),
            _ => throw new InvalidOperationException()
        };
        c.Write(c.Rd, result);
        return c.Done();
    }

    private static LiftResult UnaryInteger(Context c)
    {
        if (c.Rm != 0) return c.Reject("Reserved one-source encoding");
        var opcode = c.Field(10, 6);
        if (opcode > 4 || (opcode == 3 && c.Width != 64)) return c.Reject("Unsupported or reserved one-source operation");
        var value = c.Read(c.Rn, c.Width);
        Value result;
        if (opcode == 4)
        {
            var moving = value;
            var count = c.C(c.Width, 0);
            for (var step = c.Width / 2; step >= 1; step /= 2)
            {
                var empty = c.B.Eq(c.B.Shr(moving, c.C(c.Width, (ulong)(c.Width - step))), c.C(c.Width, 0));
                count = c.B.Add(count, c.B.Select(empty, c.C(c.Width, (ulong)step), c.C(c.Width, 0)));
                moving = c.B.Select(empty, c.B.Shl(moving, c.C(c.Width, (ulong)step)), moving);
            }
            result = c.B.Select(c.B.Eq(value, c.C(c.Width, 0)), c.C(c.Width, (ulong)c.Width), count);
        }
        else
        {
            result = c.C(c.Width, 0);
            var group = opcode == 0 ? c.Width : 8 << opcode;
            var unit = opcode == 0 ? 1 : 8;
            for (var low = 0; low < c.Width; low += unit)
            {
                var within = low % group;
                var target = low - within + group - unit - within;
                var part = c.B.Zext(c.B.Extract(value, low, unit), c.Width);
                result = c.B.Or(result, c.B.Shl(part, c.C(c.Width, (ulong)target)));
            }
        }
        c.Write(c.Rd, result);
        return c.Done();
    }

    private static LiftResult MultiplyAdd(Context c)
    {
        var left = c.Read(c.Rn, c.Width);
        var right = c.Read(c.Rm, c.Width);
        var addend = c.Read(c.Field(10, 5), c.Width);
        var product = c.B.Mul(left, right);
        c.Write(c.Rd, c.Bit(15) ? c.B.Sub(addend, product) : c.B.Add(addend, product));
        return c.Done();
    }

    private static LiftResult DirectBranch(Context c)
    {
        var target = c.Address(SignExtend((ulong)c.Field(0, 26), 26) << 2);
        if (c.Bit(31)) c.Write(30, c.Address(4));
        return c.End(MirExit.Jump(target));
    }

    private static LiftResult ConditionalBranch(Context c) => c.End(MirExit.Branch(c.Condition(c.Field(0, 4)), c.Address(SignExtend((ulong)c.Field(5, 19), 19) << 2), c.Address(4)));

    private static LiftResult CompareBranch(Context c)
    {
        var condition = c.B.Eq(c.Read(c.Rd, c.Width), c.C(c.Width, 0));
        if (c.Bit(24)) condition = c.B.BoolNot(condition);
        return c.End(MirExit.Branch(condition, c.Address(SignExtend((ulong)c.Field(5, 19), 19) << 2), c.Address(4)));
    }

    private static LiftResult TestBranch(Context c)
    {
        var bit = c.Field(19, 5) | (c.Bit(31) ? 32 : 0);
        var condition = c.B.Extract(c.Read(c.Rd, c.Width), bit, 1);
        if (!c.Bit(24)) condition = c.B.BoolNot(condition);
        return c.End(MirExit.Branch(condition, c.Address(SignExtend((ulong)c.Field(5, 14), 14) << 2), c.Address(4)));
    }

    private static LiftResult RegisterBranch(Context c)
    {
        var target = c.Read(c.Rn, 64);
        var kind = c.Word & 0xFFFFFC1F;
        if (kind == 0xD63F0000)
        {
            c.Write(30, c.Address(4));
            c.NextBranchType = c.C(2, 2);
        }
        else if (kind == 0xD61F0000)
            c.NextBranchType = c.Rn is 16 or 17 ? c.C(2, 1) : c.B.Select(c.CurrentPageGuarded, c.C(2, 3), c.C(2, 1));
        return c.End(MirExit.Jump(target));
    }

    private static LiftResult NzcvTransfer(Context c)
    {
        if (c.Bit(21))
        {
            var value = c.C(64, 0);
            var slots = new[] { "n", "z", "c", "v" };
            for (var i = 0; i < 4; i++) value = c.B.Or(value, c.B.Shl(c.B.Zext(c.Flag(slots[i]), 64), c.C(64, (ulong)(31 - i))));
            c.Write(c.Rd, value);
        }
        else
        {
            var value = c.Read(c.Rd, 64);
            var slots = new[] { "n", "z", "c", "v" };
            for (var i = 0; i < 4; i++) c.B.Write(slots[i], c.B.Extract(value, 31 - i, 1));
        }
        return c.Done();
    }
}
