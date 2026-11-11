namespace Cpp2CS.Tests.Execution;

/// <summary>ECMA-335 III.3.31/3.32 的整数 div/div.un 与 III.3.55/3.56 的 rem/rem.un。</summary>
internal static class CilIntegerDivision
{
    internal static (StackValue? Value, string? Exception) Evaluate(StackValue left, StackValue right, bool unsigned, bool remainder = false)
    {
        var width = left.Kind == StackKind.I4 ? 32 : 64;
        var x = left.Bits & Side.Mask(ulong.MaxValue, width); var y = right.Bits & Side.Mask(ulong.MaxValue, width);
        if (y == 0) return (null, "System.DivideByZeroException");
        if (!unsigned && x == 1UL << (width - 1) && y == Side.Mask(ulong.MaxValue, width)) return (null, "System.OverflowException");
        var quotient = remainder
            ? unsigned ? x % y : width == 32 ? unchecked((ulong)((int)x % (int)y)) : unchecked((ulong)((long)x % (long)y))
            : unsigned ? x / y : width == 32 ? unchecked((ulong)((int)x / (int)y)) : unchecked((ulong)((long)x / (long)y));
        return (width == 32 ? StackValue.I4((int)quotient) : StackValue.I8(quotient), null);
    }

    public const string Command = "cil-division";
    public static int Run()
    {
        var assertions = new Assertions();
        foreach (var width in new[] { 32, 64 })
            foreach (var unsigned in new[] { true, false })
            {
                var mask = Side.Mask(ulong.MaxValue, width);
                var inputs = new ulong[] { 0, 1, 2, 7, mask, mask - 1, mask - 6, mask >> 1, 1UL << (width - 1) };
                System.Numerics.BigInteger Number(ulong value) => !unsigned && value >> (width - 1) != 0
                    ? new System.Numerics.BigInteger(value) - (System.Numerics.BigInteger.One << width) : new(value);
                foreach (var x in inputs)
                    foreach (var y in inputs)
                    {
                        var actual = Evaluate(width == 32 ? StackValue.I4((int)x) : StackValue.I8(x), width == 32 ? StackValue.I4((int)y) : StackValue.I8(y), unsigned);
                        if (y == 0) { assertions.True(actual.Exception == "System.DivideByZeroException", "CIL 除零不能返回 0"); continue; }
                        var quotient = Number(x) / Number(y);
                        if (!unsigned && quotient >= System.Numerics.BigInteger.One << (width - 1))
                        { assertions.True(actual.Exception == "System.OverflowException", "CIL 有符号溢出不能回绕"); continue; }
                        assertions.True(actual.Exception is null && actual.Value?.Bits == (ulong)(quotient & mask), "CIL 商向零截断、符号和宽度与无限精度结果一致");
                        var rest = Evaluate(width == 32 ? StackValue.I4((int)x) : StackValue.I8(x), width == 32 ? StackValue.I4((int)y) : StackValue.I8(y), unsigned, remainder: true);
                        assertions.True(rest.Exception is null && rest.Value?.Bits == (ulong)((Number(x) - quotient * Number(y)) & mask), "CIL 余数与被除数同号、等于被除数减去截断商与除数之积");
                    }
            }
        return assertions.Finish("cil-division");
    }
}
