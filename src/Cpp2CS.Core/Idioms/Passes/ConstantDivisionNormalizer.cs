using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>将有完整舍入修正和误差界证明的有符号乘高位序列还原成常量除法。</summary>
internal static class ConstantDivisionNormalizer
{
    public static bool Run(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Resolve(Expr expression)
        {
            for (var depth = 0; depth < 16 && expression is Use use && definitions.TryGetValue(use.Variable, out var value); depth++)
                expression = value;
            return expression;
        }
        var changed = false;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var original = block.Statements[i];
                block.Statements[i] = ExprMap.MapOperands(original, expression => ExprMap.Map(expression,
                    value => value is Binary { Op: BinOp.Add, Width: 64 } add
                        ? Quotient(add.Left, add.Right, Resolve) ?? Quotient(add.Right, add.Left, Resolve) : null));
                changed |= !ReferenceEquals(original, block.Statements[i]);
            }
        return changed;
    }

    private static Expr? Quotient(Expr quotient, Expr correction, Func<Expr, Expr> resolve)
    {
        quotient = resolve(quotient);
        var shift = 0;
        if (quotient is Binary { Op: BinOp.AShr, Width: 64, Right: Const { Value: <= 62 } amount } shifted)
        {
            shift = (int)amount.Value;
            quotient = resolve(shifted.Left);
        }
        if (resolve(correction) is not Binary { Op: BinOp.LShr, Width: 64, Right: Const { Value: 63 } } sign
            || resolve(sign.Left) != quotient) return null;

        var product = quotient;
        Expr? added = null;
        if (quotient is Binary { Op: BinOp.Add, Width: 64 } add)
        {
            product = resolve(add.Left);
            added = add.Right;
            if (product is not Binary { Op: BinOp.MulHighS })
            {
                product = resolve(add.Right);
                added = add.Left;
            }
        }
        if (product is not Binary
            {
                Op: BinOp.MulHighS, Width: 64, Left: Use { Width: 64 } input,
                Right: Const { Width: 64, Value: > 0 } magic
            }
            || (magic.Value <= long.MaxValue ? added is not null : added != input)) return null;

        // 负乘数 m 的高位积加 n 等于 floor(n*(m+2^64)/2^64)，结果仍在有符号范围内。
        // 必须加回同一输入，并使用加回之后的符号位；此时 magic.Value 即有效的正乘数。

        var scale = UInt128.One << (64 + shift);
        var divisor = scale / magic.Value + 1;
        if (divisor < 2 || divisor > (UInt128)long.MaxValue) return null;
        var error = divisor * magic.Value - scale;
        // M*d = 2^(64+s)+e，0<e<d 保证 M=ceil(2^(64+s)/d)。
        // e<=2^(s+1) 使 |n|*e<=2^(64+s)：正数向下取整、负数加符号位后向零截断均等于 n/d。
        // e=0 时负整倍数会多加 1，因此必须拒绝；除数为正且大于 1，不引入除零或溢出异常。
        if (error == 0 || error >= divisor || error > UInt128.One << (shift + 1)) return null;
        return new Binary(BinOp.SDiv, input, Expr.C((ulong)divisor, 64), 64);
    }
}
