namespace Cpp2CS.Managed;

/// <summary>方法内唯一的局部身份；由方法体构造方分配。</summary>
public readonly record struct LocalId(int Index);

/// <summary>托管算术与位运算；整数除法与余数遵循 IL 的异常语义。</summary>
public enum BinaryOperator
{
    Add, Subtract, Multiply, SignedDivide, UnsignedDivide, SignedRemainder, UnsignedRemainder,
    And, Or, Xor, ShiftLeft, ShiftRightUnsigned, ShiftRightSigned,
    FloatAdd, FloatSubtract, FloatMultiply, FloatDivide,
}

/// <summary>托管取负、按位取反与数学函数。</summary>
public enum UnaryOperator
{
    Negate, Not, FloatNegate, Abs, Sqrt, Floor, Ceiling, Truncate, RoundToEven,
}

/// <summary>整数、浮点的数值转换与同宽位型重解释。</summary>
public enum ConversionKind
{
    ZeroExtend, SignExtend, Truncate,
    SignedIntegerToFloat, UnsignedIntegerToFloat, FloatToSignedInteger, FloatToUnsignedInteger,
    FloatToFloat, Bitcast,
}

/// <summary>整数的有符号/无符号比较；浮点 Ordered 要求两侧均非 NaN，Unordered 表示至少一侧为 NaN。</summary>
public enum ComparisonKind
{
    Equal, NotEqual, SignedLess, SignedLessOrEqual, SignedGreater, SignedGreaterOrEqual,
    UnsignedLess, UnsignedLessOrEqual, UnsignedGreater, UnsignedGreaterOrEqual,
    FloatEqual, FloatNotEqual, FloatLess, FloatLessOrEqual, FloatGreater, FloatGreaterOrEqual,
    FloatUnordered, FloatOrdered,
    FloatUnorderedOrLess, FloatUnorderedOrLessOrEqual, FloatUnorderedOrGreater,
    FloatUnorderedOrGreaterOrEqual, FloatUnorderedOrEqual, FloatUnorderedOrNotEqual,
}
