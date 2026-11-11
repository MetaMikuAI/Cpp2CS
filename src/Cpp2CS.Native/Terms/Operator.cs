using System.Collections.Immutable;

namespace Cpp2CS.Native.Terms;

/// <summary>上层可定义不可变的值对象；Name 必须完整编码值身份并带词汇域，Accepts 只检查形状。</summary>
public abstract record Operator
{
    public abstract string Name { get; }
    public abstract bool Accepts(int resultWidth, ImmutableArray<int> operandWidths);
}

/// <summary>
/// 整数以无类型位型表示。浮点格式为 IEEE 754 binary16/32/64/128，默认舍入为就近取偶，支持次正规数，不表示异常标志。
/// NaN 结果的符号与载荷不作规定：任何 NaN 都是合法的结果，比较两个结果时所有 NaN 视为相同；求值器取正号、最高尾数位置位的静默 NaN。
/// 逐位的符号运算（取负、取绝对值）只改符号位。前端不需要编码目标的 NaN 载荷行为。
/// 未定义情形不赋予目标行为；前端须用选择等显式编码除零得零、饱和转换这类目标行为。
/// </summary>
public enum CoreOperation
{
    /// <summary>整数加法，结果模 2^位宽。</summary>
    Add,
    /// <summary>整数减法，结果模 2^位宽。</summary>
    Subtract,
    /// <summary>整数乘法的低半部分，结果模 2^位宽。</summary>
    Multiply,
    /// <summary>二补码有符号除法，向零截断；除零及最小值除以 -1 未定义。</summary>
    SignedDivide,
    /// <summary>无符号除法；除零未定义。</summary>
    UnsignedDivide,
    /// <summary>有符号余数，与向零截断的商对应；除零及最小值除以 -1 未定义。</summary>
    SignedRemainder,
    /// <summary>无符号余数；除零未定义。</summary>
    UnsignedRemainder,
    /// <summary>二补码取负，结果模 2^位宽。</summary>
    Negate,
    /// <summary>逐位与。</summary>
    And,
    /// <summary>逐位或。</summary>
    Or,
    /// <summary>逐位异或。</summary>
    Xor,
    /// <summary>逐位取反。</summary>
    Not,
    /// <summary>左移，补零；无符号移位量不小于位宽时未定义。</summary>
    ShiftLeft,
    /// <summary>逻辑右移，补零；无符号移位量不小于位宽时未定义。</summary>
    LogicalShiftRight,
    /// <summary>算术右移，补符号位；无符号移位量不小于位宽时未定义。</summary>
    ArithmeticShiftRight,
    /// <summary>位型相等返回 1，否则 0。</summary>
    Equal,
    /// <summary>位型不等返回 1，否则 0。</summary>
    NotEqual,
    /// <summary>二补码有符号小于返回 1，否则 0。</summary>
    SignedLess,
    /// <summary>二补码有符号小于等于返回 1，否则 0。</summary>
    SignedLessEqual,
    /// <summary>无符号小于返回 1，否则 0。</summary>
    UnsignedLess,
    /// <summary>无符号小于等于返回 1，否则 0。</summary>
    UnsignedLessEqual,
    /// <summary>IEEE 754 加法；任一操作数为 NaN 时结果为 NaN。</summary>
    FloatAdd,
    /// <summary>IEEE 754 减法；任一操作数为 NaN 时结果为 NaN。</summary>
    FloatSubtract,
    /// <summary>IEEE 754 乘法；任一操作数为 NaN 时结果为 NaN。</summary>
    FloatMultiply,
    /// <summary>IEEE 754 除法；有限非零数除以零为带符号无穷，0/0 为 NaN。</summary>
    FloatDivide,
    /// <summary>IEEE 754 remainder，商取最近整数、平局取偶；零除数或无穷被除数产生 NaN。</summary>
    FloatRemainder,
    /// <summary>翻转符号位，保留 NaN 的其余位。</summary>
    FloatNegate,
    /// <summary>清除符号位，保留 NaN 的其余位。</summary>
    FloatAbs,
    /// <summary>IEEE 754 平方根；负数（-0 除外）产生 NaN。</summary>
    FloatSqrt,
    /// <summary>有序相等；任一 NaN 返回 0，正负零相等。</summary>
    FloatEqual,
    /// <summary>无序或不等；任一 NaN 返回 1，正负零相等。</summary>
    FloatNotEqual,
    /// <summary>有序小于；任一 NaN 返回 0。</summary>
    FloatLess,
    /// <summary>有序小于等于；任一 NaN 返回 0。</summary>
    FloatLessEqual,
    /// <summary>两操作数都不是 NaN 返回 1，否则 0。</summary>
    FloatOrdered,
    /// <summary>任一操作数为 NaN 返回 1，否则 0。</summary>
    FloatUnordered,
    /// <summary>高位补零扩展。</summary>
    ZeroExtend,
    /// <summary>复制最高位扩展。</summary>
    SignExtend,
    /// <summary>保留低位，丢弃高位。</summary>
    Truncate,
    /// <summary>二补码有符号整数转浮点，按就近取偶舍入。</summary>
    SignedToFloat,
    /// <summary>无符号整数转浮点，按就近取偶舍入。</summary>
    UnsignedToFloat,
    /// <summary>浮点向零截断转有符号整数；NaN、无穷或截断结果越界时未定义。</summary>
    FloatToSigned,
    /// <summary>浮点向零截断转无符号整数；NaN、无穷或截断结果越界时未定义。</summary>
    FloatToUnsigned,
    /// <summary>IEEE 754 浮点格式转换，按就近取偶舍入；NaN 产生目标格式的 NaN。</summary>
    FloatConvert,
    /// <summary>一位条件为 1 取第二项，否则取第三项；未选分支不影响结果。</summary>
    Select,
    /// <summary>循环右移；无符号移位量对位宽取模。</summary>
    RotateRight,
    /// <summary>二补码有符号乘积的高半位型；先在双倍位宽精确相乘。</summary>
    SignedMultiplyHigh,
    /// <summary>无符号乘积的高半位型；先在双倍位宽精确相乘。</summary>
    UnsignedMultiplyHigh,
    /// <summary>从最高位计连续零位数；全零返回位宽。</summary>
    CountLeadingZeros,
    /// <summary>返回置位数量。</summary>
    PopulationCount,
    /// <summary>反转全部位的次序。</summary>
    ReverseBits,
    /// <summary>反转字节次序，字节内位序不变；位宽必须为 8 的倍数。</summary>
    ReverseBytes,
    /// <summary>IEEE 754 minimum；任一 NaN 传播 NaN，-0 小于 +0。</summary>
    FloatMinimum,
    /// <summary>IEEE 754 maximum；任一 NaN 传播 NaN，-0 小于 +0。</summary>
    FloatMaximum,
    /// <summary>IEEE 754-2019 minimumNumber；单个 NaN（包括信号 NaN）取数值，两个 NaN 产生 NaN；-0 小于 +0。</summary>
    FloatMinimumNumber,
    /// <summary>IEEE 754-2019 maximumNumber；单个 NaN（包括信号 NaN）取数值，两个 NaN 产生 NaN；-0 小于 +0。</summary>
    FloatMaximumNumber,
    /// <summary>向负无穷取整，结果仍为浮点；保持零的符号与无穷，NaN 传播。</summary>
    FloatFloor,
    /// <summary>向正无穷取整，结果仍为浮点；保持零的符号与无穷，NaN 传播。</summary>
    FloatCeiling,
    /// <summary>向零取整，结果仍为浮点；保持零的符号与无穷，NaN 传播。</summary>
    FloatTruncate,
    /// <summary>就近取偶取整，结果仍为浮点；保持零的符号与无穷，NaN 传播。</summary>
    FloatRoundToEven,
    /// <summary>IEEE 754 融合 a*b+c，仅最终舍入一次；0*无穷或无穷乘积加反号无穷产生 NaN。</summary>
    FloatFusedMultiplyAdd,
}

public sealed record CoreOperator(CoreOperation Operation) : Operator
{
    public override string Name => "core." + Operation;
    public override bool Accepts(int resultWidth, ImmutableArray<int> w) => Accepts(resultWidth, w.AsSpan());

    internal bool Accepts(int resultWidth, ReadOnlySpan<int> w)
    {
        if (!Enum.IsDefined(Operation) || resultWidth <= 0) return false;
        var sameWidth = true;
        foreach (var width in w)
        {
            if (width <= 0) return false;
            sameWidth &= width == resultWidth;
        }
        bool Float(int width) => width is 16 or 32 or 64 or 128;
        return Operation switch
        {
            CoreOperation.Select => w.Length == 3 && w[0] == 1 && w[1] == resultWidth && w[2] == resultWidth,
            CoreOperation.ZeroExtend or CoreOperation.SignExtend => w.Length == 1 && resultWidth > w[0],
            CoreOperation.Truncate => w.Length == 1 && resultWidth < w[0],
            CoreOperation.SignedToFloat or CoreOperation.UnsignedToFloat => w.Length == 1 && Float(resultWidth),
            CoreOperation.FloatToSigned or CoreOperation.FloatToUnsigned => w.Length == 1 && Float(w[0]),
            CoreOperation.FloatConvert => w.Length == 1 && Float(w[0]) && Float(resultWidth),
            CoreOperation.ReverseBytes => w.Length == 1 && w[0] == resultWidth && resultWidth % 8 == 0,
            CoreOperation.CountLeadingZeros or CoreOperation.PopulationCount or CoreOperation.ReverseBits => w.Length == 1 && w[0] == resultWidth,
            CoreOperation.FloatFusedMultiplyAdd => w.Length == 3 && sameWidth && Float(resultWidth),
            >= CoreOperation.FloatMinimum and <= CoreOperation.FloatMaximumNumber => w.Length == 2 && sameWidth && Float(resultWidth),
            >= CoreOperation.FloatFloor and <= CoreOperation.FloatRoundToEven => w.Length == 1 && w[0] == resultWidth && Float(resultWidth),
            CoreOperation.Negate or CoreOperation.Not => w.Length == 1 && w[0] == resultWidth,
            CoreOperation.FloatNegate or CoreOperation.FloatAbs or CoreOperation.FloatSqrt =>
                w.Length == 1 && w[0] == resultWidth && Float(resultWidth),
            >= CoreOperation.Equal and <= CoreOperation.UnsignedLessEqual => w.Length == 2 && w[0] == w[1] && resultWidth == 1,
            >= CoreOperation.FloatEqual and <= CoreOperation.FloatUnordered => w.Length == 2 && w[0] == w[1] && Float(w[0]) && resultWidth == 1,
            >= CoreOperation.FloatAdd and <= CoreOperation.FloatRemainder => w.Length == 2 && sameWidth && Float(resultWidth),
            _ => w.Length == 2 && sameWidth
        };
    }
}
