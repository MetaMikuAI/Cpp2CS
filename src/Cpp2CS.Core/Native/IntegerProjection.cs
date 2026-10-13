using Cpp2CS.IR;

namespace Cpp2CS.Native;

// 表达式的整数类型必须能表示当前全部位；ABI 未定义高位不能由强转补齐。
public static class IntegerProjection
{
    public static int Width(string type) => type switch
    {
        "int8_t" or "uint8_t" => 8, "int16_t" or "uint16_t" => 16,
        "int32_t" or "uint32_t" => 32, "int64_t" or "uint64_t" => 64, _ => 0
    };
    public static Expression? Bits(NativeValue value)
    {
        var width = Width(value.Type);
        if (width == 0 || value.Expression is SliceExpression || value.Bits.Width < width || value.Bits.Width > 64) return null;
        if (width == value.Bits.Width) return value.Expression;
        return BitOps.Slice(value.Bits, width, value.Bits.Width - width) is ConstantBits { Value.IsZero: true }
            ? new OperationExpression(ValueOperation.IntegerCast, $"uint{width}_t", [value.Expression]) : null;
    }
}
