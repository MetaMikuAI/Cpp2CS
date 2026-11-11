using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>校验与写出共用的运算支持范围。</summary>
internal static class CilOperators
{
    public static OpCode? Binary(BinaryOperator op) => op switch
    {
        BinaryOperator.Add or BinaryOperator.FloatAdd => OpCodes.Add,
        BinaryOperator.Subtract or BinaryOperator.FloatSubtract => OpCodes.Sub,
        BinaryOperator.Multiply or BinaryOperator.FloatMultiply => OpCodes.Mul,
        BinaryOperator.FloatDivide or BinaryOperator.SignedDivide => OpCodes.Div,
        BinaryOperator.UnsignedDivide => OpCodes.Div_Un,
        BinaryOperator.SignedRemainder => OpCodes.Rem,
        BinaryOperator.UnsignedRemainder => OpCodes.Rem_Un,
        BinaryOperator.And => OpCodes.And,
        BinaryOperator.Or => OpCodes.Or,
        BinaryOperator.Xor => OpCodes.Xor,
        BinaryOperator.ShiftLeft => OpCodes.Shl,
        BinaryOperator.ShiftRightUnsigned => OpCodes.Shr_Un,
        BinaryOperator.ShiftRightSigned => OpCodes.Shr,
        _ => null,
    };

    public static OpCode? Unary(UnaryOperator op) => op switch
    {
        UnaryOperator.Not => OpCodes.Not,
        UnaryOperator.Negate or UnaryOperator.FloatNegate => OpCodes.Neg,
        _ => null,
    };

    public static string? Math(UnaryOperator op) => op switch
    {
        UnaryOperator.Abs => "Abs",
        UnaryOperator.Sqrt => "Sqrt",
        UnaryOperator.Floor => "Floor",
        UnaryOperator.Ceiling => "Ceiling",
        UnaryOperator.Truncate => "Truncate",
        UnaryOperator.RoundToEven => "Round",
        _ => null,
    };
}
