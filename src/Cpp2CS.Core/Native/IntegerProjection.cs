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
        if (width == 0 || value.Expression is SliceExpression || value.Bits.Width > 64) return null;
        if (value.Bits.Width < width)
            return value.Expression is OperationExpression { Operation: ValueOperation.ExtractBits, Arguments: [_, _, ConstantExpression count] } && count.Value == value.Bits.Width ||
                value.Expression is ConstantExpression { Value: >= 0 } number && value.Bits is ConstantBits constant && constant.Value == number.Value ? value.Expression : null;
        if (width == value.Bits.Width) return value.Expression;
        return BitOps.Slice(value.Bits, width, value.Bits.Width - width) is ConstantBits { Value.IsZero: true }
            ? new OperationExpression(ValueOperation.IntegerCast, $"uint{width}_t", [value.Expression]) : null;
    }
    public static NativeValue? Extract(NativeValue value, int offset, int width)
    {
        var available = Width(value.Type);
        if (available == 0) return null;
        var expression = value.Expression;
        var start = offset;
        if (Bits(value) is { } complete)
        {
            available = value.Bits.Width;
            expression = complete;
        }
        else while (expression is SliceExpression slice)
        {
            start = checked(start + slice.BitOffset);
            expression = slice.Value;
        }
        if (start < 0 || width <= 0 || start + width > available) return null;
        var bits = BitOps.Slice(value.Bits, offset, width);
        if (start == 0 && width == available) return new(bits, value.Type, expression);
        var type = width <= 32 ? "uint32_t" : "uint64_t";
        return new(bits, type, new OperationExpression(ValueOperation.ExtractBits, type, [expression, new ConstantExpression(start), new ConstantExpression(width)]));
    }
}
