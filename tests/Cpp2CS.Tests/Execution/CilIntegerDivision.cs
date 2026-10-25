namespace Cpp2CS.Tests.Execution;

/// <summary>ECMA-335 III.3.31/3.32 的整数 div/div.un；异常与 ARM64 的零/回绕结果严格区分。</summary>
internal static class CilIntegerDivision
{
    internal static (StackValue? Value, string? Exception) Evaluate(StackValue left, StackValue right, bool unsigned)
    {
        var width = left.Kind == StackKind.I4 ? 32 : 64;
        var x = left.Bits & Ir.Expr.Mask(width); var y = right.Bits & Ir.Expr.Mask(width);
        if (y == 0) return (null, "System.DivideByZeroException");
        if (!unsigned && x == 1UL << (width - 1) && y == Ir.Expr.Mask(width)) return (null, "System.OverflowException");
        var quotient = unsigned ? x / y : width == 32 ? unchecked((ulong)((int)x / (int)y)) : unchecked((ulong)((long)x / (long)y));
        return (width == 32 ? StackValue.I4((int)quotient) : StackValue.I8(quotient), null);
    }

    [Command("cil-division", "CIL 整数除法与无限精度算术的独立对照", Gate = Gate.Unit)]
    public static int Check()
    {
        var assertions = new Assertions();
        foreach (var width in new[] { 32, 64 })
            foreach (var unsigned in new[] { true, false })
            {
                var mask = Ir.Expr.Mask(width);
                var inputs = new ulong[] { 0, 1, 2, 7, mask, mask - 1, mask - 6, mask >> 1, 1UL << (width - 1) };
                System.Numerics.BigInteger Number(ulong value) => !unsigned && value >> (width - 1) != 0
                    ? new System.Numerics.BigInteger(value) - (System.Numerics.BigInteger.One << width) : new(value);
                foreach (var x in inputs)
                    foreach (var y in inputs)
                    {
                        var actual = Evaluate(width == 32 ? StackValue.I4((int)x) : StackValue.I8(x), width == 32 ? StackValue.I4((int)y) : StackValue.I8(y), unsigned);
                        if (y == 0) { assertions.Equal("System.DivideByZeroException", actual.Exception, "CIL 除零不能返回 0"); continue; }
                        var quotient = Number(x) / Number(y);
                        if (!unsigned && quotient >= System.Numerics.BigInteger.One << (width - 1))
                        { assertions.Equal("System.OverflowException", actual.Exception, "CIL 有符号溢出不能回绕"); continue; }
                        assertions.True(actual.Exception is null && actual.Value?.Bits == (ulong)(quotient & mask), "CIL 商向零截断、符号和宽度与无限精度结果一致");
                    }
            }
        return assertions.Finish("cil-division");
    }
}
