using Cpp2CS.Ir;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>校验与写出共用的运算支持范围。</summary>
internal static class CilOperators
{
    public static OpCode? Binary(BinOp op) => op switch
    {
        BinOp.Add or BinOp.FAdd => OpCodes.Add,
        BinOp.Sub or BinOp.FSub => OpCodes.Sub,
        BinOp.Mul or BinOp.FMul => OpCodes.Mul,
        BinOp.FDiv => OpCodes.Div,
        BinOp.And => OpCodes.And,
        BinOp.Or => OpCodes.Or,
        BinOp.Xor => OpCodes.Xor,
        BinOp.Shl => OpCodes.Shl,
        BinOp.LShr => OpCodes.Shr_Un,
        BinOp.AShr => OpCodes.Shr,
        _ => null,
    };

    /// <summary>需要按原生语义展开的运算。取余只来自常量除法的还原，除数是非零常量（有符号时也不是 -1）。</summary>
    public static bool NativeArithmetic(BinOp op) => op is
        BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem or BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber;

    public static OpCode? Unary(UnOp op) => op switch
    {
        UnOp.Not => OpCodes.Not,
        UnOp.Neg or UnOp.FNeg => OpCodes.Neg,
        _ => null,
    };

    public static string? Math(UnOp op) => op switch
    {
        UnOp.FAbs => "Abs",
        UnOp.FSqrt => "Sqrt",
        UnOp.FFloor => "Floor",
        UnOp.FCeil => "Ceiling",
        UnOp.FTrunc => "Truncate",
        UnOp.FRoundEven => "Round",
        _ => null,
    };
}
