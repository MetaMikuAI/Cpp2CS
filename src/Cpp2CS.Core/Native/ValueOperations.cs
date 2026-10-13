namespace Cpp2CS.Native;

public enum ValueOperation { SignedToFloat, ZeroExtendWord, Unsigned, IntegerCast, FloatDivide, Ceiling, FloatToSignedCeiling, BitCast, Add, Subtract, Select, ArrayElement, NewArray, ReferenceSelect, SignExtend, ShiftLeft, LogicalShiftRight, ArithmeticShiftRight, BitAnd, BitOr, BitXor, Multiply }
internal sealed record IndexedArrayAddress(Expression Array, Expression Index, HeaderField Elements, string ArrayType, int Offset = 0) : Expression;
public sealed record OperationExpression(ValueOperation Operation, string Type, Expression[] Arguments) : Expression;

// 数值操作保留结果类型和舍入方式；数组元素是可取地址的左值。
public static class ValueOperations
{
    public static string Write(OperationExpression operation)
    {
        var a = operation.Arguments.Select(SemanticWriter.Expression).ToArray();
        var type = operation.Type switch { "int8_t" => "sbyte", "uint8_t" => "byte", "int16_t" => "short", "uint16_t" => "ushort",
            "int32_t" => "int", "uint32_t" => "uint", "int64_t" => "long", "uint64_t" => "ulong", _ => operation.Type };
        return operation.Operation switch
        {
            ValueOperation.SignedToFloat => $"(({type})unchecked(({(a[1] == "32" ? "int" : "long")})({a[0]})))",
            ValueOperation.ZeroExtendWord => $"unchecked((long)(uint)({a[0]}))",
            ValueOperation.Unsigned => $"unchecked(({(operation.Type == "uint32_t" ? "uint" : "ulong")})({a[0]}))",
            ValueOperation.IntegerCast => $"unchecked(({type})({a[0]}))",
            ValueOperation.FloatDivide => $"(({type})({a[0]} / {a[1]}))",
            ValueOperation.Ceiling => $"{(type == "float" ? "MathF" : "Math")}.Ceiling({a[0]})",
            ValueOperation.FloatToSignedCeiling => $"Cpp2CS.Native.NumericSemantics.CeilingTo{(type == "int" ? "Int32" : "Int64")}({a[0]})",
            ValueOperation.BitCast => type switch
            {
                "float" when operation.Arguments[0] is ConstantExpression { Value: 2139095040 } => "float.PositiveInfinity",
                "float" => $"BitConverter.Int32BitsToSingle(unchecked((int){a[0]}))",
                "double" => $"BitConverter.Int64BitsToDouble(unchecked((long){a[0]}))",
                "int" => $"BitConverter.SingleToInt32Bits({a[0]})",
                "long" => $"BitConverter.DoubleToInt64Bits({a[0]})",
                _ => throw new InvalidOperationException("不支持的位转换类型")
            },
            ValueOperation.Add or ValueOperation.Subtract or ValueOperation.Multiply => $"unchecked(({type})({a[0]}) {(operation.Operation == ValueOperation.Add ? "+" : operation.Operation == ValueOperation.Subtract ? "-" : "*")} ({type})({a[1]}))",
            ValueOperation.Select => $"({a[0]} ? unchecked(({type})({a[1]})) : unchecked(({type})({a[2]})))",
            ValueOperation.ReferenceSelect => $"({a[0]} ? {a[1]} : {a[2]})",
            ValueOperation.SignExtend => $"unchecked(({type})({(a[1] == "8" ? "sbyte" : a[1] == "16" ? "short" : a[1] == "32" ? "int" : "long")})({a[0]}))",
            ValueOperation.ShiftLeft => $"unchecked(({type})({a[0]}) << {a[1]})",
            ValueOperation.ArithmeticShiftRight => $"(unchecked(({type})({a[0]})) >> {a[1]})",
            ValueOperation.LogicalShiftRight => $"unchecked(({type})(({(type == "int" ? "uint" : "ulong")})({a[0]}) >> {a[1]}))",
            ValueOperation.BitAnd or ValueOperation.BitOr or ValueOperation.BitXor => $"unchecked(({type})({a[0]}) {(operation.Operation == ValueOperation.BitAnd ? "&" : operation.Operation == ValueOperation.BitOr ? "|" : "^")} ({type})({a[1]}))",
            ValueOperation.ArrayElement => $"{a[0]}[{a[1]}]",
            ValueOperation.NewArray => $"new {type}[{a[0]}]",
            _ => throw new InvalidOperationException("未实现的类型化操作")
        };
    }
}

// ARM64 FCVTPS 的数值结果：向正无穷取整、越界饱和、NaN 为零。
// 托管视图不模拟 FPCR 陷阱或 FPSR 状态位。
public static class NumericSemantics
{
    public static int CeilingToInt32(double value) => double.IsNaN(value) ? 0 :
        value >= int.MaxValue ? int.MaxValue : value <= int.MinValue ? int.MinValue : (int)Math.Ceiling(value);
    public static long CeilingToInt64(double value) => double.IsNaN(value) ? 0 :
        value >= 9223372036854775808d ? long.MaxValue : value <= -9223372036854775808d ? long.MinValue : (long)Math.Ceiling(value);
}
