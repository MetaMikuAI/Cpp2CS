using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Control;

/// <summary>沿路径求值只含常量和已知局部的条件：finally 的去向和状态机的分派都由具体的值决定。按 32 位整数计算，更宽的值不求值。</summary>
internal static class ConstantConditions
{
    /// <param name="leaf">已知的叶子（局部或字段）的值，未知时返回空。</param>
    public static long? Evaluate(ManagedValue value, Func<ManagedValue, long?> leaf)
    {
        if (leaf(value) is { } known) return known;
        long? Sub(ManagedValue operand) => Evaluate(operand, leaf);
        switch (value)
        {
            case ConstantValue { Width: <= 32 } constant:
                return (int)constant.Bits;
            case NegatedValue negated when Sub(negated.Operand) is { } operand:
                return operand == 0 ? 1 : 0;
            case ComparisonValue comparison when Sub(comparison.Left) is { } a && Sub(comparison.Right) is { } b:
                return Compare(comparison.Condition, a, b);
            case ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate or ConvKind.Bitcast, Width: <= 32 } conversion when Sub(conversion.Operand) is { } operand:
                return (int)operand;
            case BinaryValue { Width: <= 32 } binary when Sub(binary.Left) is { } a && Sub(binary.Right) is { } b:
                var (x, y) = ((int)a, (int)b);
                return binary.Op switch
                {
                    BinOp.Add => x + y,
                    BinOp.Sub => x - y,
                    BinOp.And => x & y,
                    BinOp.Or => x | y,
                    BinOp.Xor => x ^ y,
                    BinOp.Shl => x << (y & 31),
                    BinOp.LShr => (int)((uint)x >> (y & 31)),
                    BinOp.AShr => x >> (y & 31),
                    _ => null,
                };
            default:
                return null;
        }
    }

    private static long? Compare(Cond condition, long a, long b)
    {
        var (ua, ub) = ((uint)a, (uint)b);
        bool? result = condition switch
        {
            Cond.Eq => a == b, Cond.Ne => a != b,
            Cond.Slt => a < b, Cond.Sle => a <= b, Cond.Sgt => a > b, Cond.Sge => a >= b,
            Cond.Ult => ua < ub, Cond.Ule => ua <= ub, Cond.Ugt => ua > ub, Cond.Uge => ua >= ub,
            _ => null,
        };
        return result is { } known ? known ? 1 : 0 : null;
    }
}
