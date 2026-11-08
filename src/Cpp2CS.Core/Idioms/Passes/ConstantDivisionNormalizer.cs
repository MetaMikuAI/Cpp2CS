using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>
/// 将有完整舍入修正和误差界证明的乘高位序列还原成常量除法：有符号带符号位修正，无符号带被除数上界。
/// 已还原的商再乘回除数、从同一被除数中减去时还原成取余。
/// </summary>
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
                block.Statements[i] = ExprMap.MapOperands(original, expression => ExprMap.Map(expression, value => value switch
                {
                    Binary { Op: BinOp.Add, Width: 32 or 64 } add
                        => Quotient(add.Left, add.Right, add.Width, Resolve) ?? Quotient(add.Right, add.Left, add.Width, Resolve),
                    Binary { Op: BinOp.LShr, Width: 64, Right: Const { Value: <= 63 } amount } shifted
                        => UnsignedQuotient(Resolve(shifted.Left), (int)amount.Value, Resolve),
                    Binary { Op: BinOp.MulHighU } => UnsignedQuotient(value, 0, Resolve),
                    Binary { Op: BinOp.Sub, Width: 64 } sub => Remainder(sub, Resolve),
                    _ => null,
                }));
                changed |= !ReferenceEquals(original, block.Statements[i]);
            }
        return changed;
    }

    private static Expr? Quotient(Expr quotient, Expr correction, int width, Func<Expr, Expr> resolve)
    {
        quotient = resolve(quotient);
        var shift = 0;
        // 仅观察低位时，逻辑右移与算术右移在这些位上相同。
        if (quotient is Binary { Op: BinOp.AShr or BinOp.LShr, Width: 64, Right: Const { Value: <= 62 } amount } shifted
            && (shifted.Op == BinOp.AShr || width <= 64 - (int)amount.Value))
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
                Op: BinOp.MulHighS, Width: 64, Left: { Width: 64 } input,
                Right: Const { Width: 64, Value: > 0 } magic
            }
            || !ExprMap.Walk(input).All(e => e is Use or Const or Binary or Unary or Ir.Convert or Compare or Select or Extract or Insert)
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
        return Fold.Convert(ConvKind.Truncate, new Binary(BinOp.SDiv, input, Expr.C((ulong)divisor, 64), 64), width);
    }

    /// <summary>
    /// floor(n*M/2^(64+s))：取 d=ceil(2^(64+s)/M)，误差 e=M*d-2^(64+s)。n=qd+r 时结果为 q+floor((r+n*e/2^(64+s))/d)，
    /// 被除数上界 N 满足 N*e&lt;2^(64+s) 时对所有 n&lt;=N 等于 n/d（Granlund–Montgomery）。上界取自移位、掩码和零扩展。
    /// </summary>
    private static Expr? UnsignedQuotient(Expr product, int shift, Func<Expr, Expr> resolve)
    {
        if (product is not Binary { Op: BinOp.MulHighU, Width: 64, Left: { Width: 64 } input, Right: Const { Width: 64, Value: > 0 } magic }
            || !ExprMap.Walk(input).All(e => e is Use or Const or Binary or Unary or Ir.Convert or Compare or Select or Extract or Insert)) return null;
        var scale = UInt128.One << (64 + shift);
        var divisor = (scale + magic.Value - 1) / magic.Value;
        if (divisor < 2 || divisor > ulong.MaxValue) return null;
        var error = divisor * magic.Value - scale;
        if (UpperBound(input, resolve, 0) * error >= scale) return null;
        return new Binary(BinOp.UDiv, input, Expr.C((ulong)divisor, 64), 64);
    }

    /// <summary>n*c-(n/d)*(c*d) 按模 2^64 等于 (n%d)*c：截断除法下 n-(n/d)*d 即余数，有符号与无符号相同。</summary>
    private static Expr? Remainder(Binary sub, Func<Expr, Expr> resolve)
    {
        if (resolve(sub.Right) is not Binary { Op: BinOp.Mul, Width: 64 } product) return null;
        var (quotient, scaled) = resolve(product.Right) is Const right ? (resolve(product.Left), right)
            : resolve(product.Left) is Const left ? (resolve(product.Right), left) : (null, null);
        if (quotient is not Binary { Op: BinOp.UDiv or BinOp.SDiv, Width: 64, Right: Const divisor } division || scaled is null) return null;
        var (dividend, factor) = resolve(sub.Left) switch
        {
            Binary { Op: BinOp.Mul, Right: Const c } m => (m.Left, c.Value),
            Binary { Op: BinOp.Mul, Left: Const c } m => (m.Right, c.Value),
            Binary { Op: BinOp.Shl, Right: Const { Value: < 64 } c } m => (m.Left, 1UL << (int)c.Value),
            var plain => (plain, 1UL),
        };
        if (dividend.Width != 64 || resolve(dividend) != resolve(division.Left) || unchecked(factor * divisor.Value) != scaled.Value) return null;
        var remainder = new Binary(division.Op == BinOp.UDiv ? BinOp.URem : BinOp.SRem, division.Left, divisor, 64);
        return factor == 1 ? remainder : new Binary(BinOp.Mul, remainder, Expr.C(factor, 64), 64);
    }

    private static UInt128 UpperBound(Expr expression, Func<Expr, Expr> resolve, int depth)
    {
        // 截取低位的读取不大于原值，也不大于该宽度的最大值。
        var limit = (UInt128.One << expression.Width) - 1;
        if (depth > 16) return limit;
        var bound = resolve(expression) switch
        {
            Const constant => constant.Value,
            Binary { Op: BinOp.LShr, Right: Const { Value: < 64 } amount } shifted => UpperBound(shifted.Left, resolve, depth + 1) >> (int)amount.Value,
            Binary { Op: BinOp.And, Right: Const mask } masked => UInt128.Min(mask.Value, UpperBound(masked.Left, resolve, depth + 1)),
            Binary { Op: BinOp.And, Left: Const mask } masked => UInt128.Min(mask.Value, UpperBound(masked.Right, resolve, depth + 1)),
            Ir.Convert { Kind: ConvKind.ZeroExtend, Operand: var operand } => UpperBound(operand, resolve, depth + 1),
            var resolved => (UInt128.One << resolved.Width) - 1,
        };
        return UInt128.Min(bound, limit);
    }
}
