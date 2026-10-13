using Cpp2CS.IR;

namespace Cpp2CS.Native;

// 保留数组根、元素索引和字节偏移；索引的来源与机器指令的排列无关。
internal static class ArrayAddressProjection
{
    public static NativeValue? Add(string identity, NativeValue receiver, NativeValue delta, HeaderLayout layouts)
    {
        if (Describe(receiver, layouts) is not { } address || delta.Bits.Width != 64 || IntegerProjection.Bits(delta) is not { } integer) return null;
        var size = layouts.Size(address.Elements.Type);
        if (size <= 0) return null;
        if (Unwrap(integer) is ConstantExpression { Value: >= int.MinValue and <= int.MaxValue } constant)
        {
            if (constant.Value == 0) return receiver;
            var offset = (long)address.Offset + constant.Value;
            if (offset is < int.MinValue or > int.MaxValue) return null;
            // 普通数组头中的地址仍由字段布局解释。
            if (receiver.Expression is not (IndexedArrayAddress or AddressOfExpression) && offset < address.Elements.Offset) return null;
            address = address with { Offset = (int)offset };
        }
        else
        {
            if (address.Index is not ConstantExpression baseIndex || ScaledIndex(integer, size) is not { } index) return null;
            var offset = (System.Numerics.BigInteger)baseIndex.Value * size + address.Offset;
            if (offset < int.MinValue || offset > int.MaxValue) return null;
            address = address with { Index = index, Offset = (int)offset };
        }
        var location = Element(address, 0, size, layouts);
        return location is null
            ? new(new InputBits(identity, 64), "array-address", address)
            : new(new InputBits(identity, 64), address.Elements.Type + "*", new AddressOfExpression(location) { RootType = address.ArrayType });
    }

    public static OperationExpression? Element(NativeValue receiver, int offset, int size, HeaderLayout layouts) =>
        Describe(receiver, layouts) is { } address ? Element(address, offset, size, layouts) : null;

    private static OperationExpression? Element(IndexedArrayAddress address, int offset, int size, HeaderLayout layouts)
    {
        var bytes = (long)address.Offset + offset - address.Elements.Offset;
        if (size <= 0 || size != layouts.Size(address.Elements.Type) || bytes < 0 || bytes % size != 0) return null;
        var index = address.Index;
        if (bytes != 0) index = index is ConstantExpression constant
            ? new ConstantExpression(checked(constant.Value + bytes / size))
            : new OperationExpression(ValueOperation.Add, "int64_t", [index, new ConstantExpression(bytes / size)]);
        return new(ValueOperation.ArrayElement, address.Elements.Type, [address.Array, index]);
    }

    private static IndexedArrayAddress? Describe(NativeValue receiver, HeaderLayout layouts)
    {
        if (receiver.Expression is IndexedArrayAddress indexed) return indexed;
        if (receiver.Expression is AddressOfExpression address)
            return address is { RootType: { } root, Target: OperationExpression { Operation: ValueOperation.ArrayElement, Arguments: [var array, var index] } } &&
                layouts.ArrayElements(root) is { } element ? new(array, index, element, root, element.Offset) : null;
        return receiver.Type.EndsWith("_array*") && layouts.ArrayElements(receiver.Type) is { } elements
            ? new(receiver.Expression, new ConstantExpression(0), elements, receiver.Type) : null;
    }

    private static Expression? ScaledIndex(Expression expression, int size)
    {
        var operation = Unwrap(expression);
        Expression? index = operation switch
        {
            OperationExpression { Operation: ValueOperation.ShiftLeft, Type: "int64_t", Arguments: [var value, ConstantExpression { Value: >= 0 and < 31 } shift] }
                when (1L << (int)shift.Value) == size => value,
            OperationExpression { Operation: ValueOperation.Multiply, Type: "int64_t", Arguments: [var left, var right] }
                when Unwrap(right) is ConstantExpression constant && constant.Value == size => left,
            OperationExpression { Operation: ValueOperation.Multiply, Type: "int64_t", Arguments: [var left, var right] }
                when Unwrap(left) is ConstantExpression constant && constant.Value == size => right,
            _ when size == 1 => expression,
            _ => null
        };
        return index is not null && BoundedIndex(index) ? index : null;
    }

    // 先确认缩放不会产生 32/64 位回绕，再把字节运算改写为托管数组索引。
    private static bool BoundedIndex(Expression expression) => Unwrap(expression) switch
    {
        ConstantExpression { Value: >= int.MinValue and <= uint.MaxValue } => true,
        OperationExpression { Operation: ValueOperation.SignExtend, Type: "int64_t", Arguments: [_, ConstantExpression { Value: 8 or 16 or 32 }] } => true,
        OperationExpression { Operation: ValueOperation.IntegerCast, Type: "int8_t" or "uint8_t" or "int16_t" or "uint16_t" or "int32_t" or "uint32_t" } => true,
        OperationExpression { Operation: ValueOperation.ZeroExtendWord } => true,
        OperationExpression { Operation: ValueOperation.Add, Type: "int64_t", Arguments: [var left, var right] } =>
            IsZero(left) && BoundedIndex(right) || IsZero(right) && BoundedIndex(left),
        OperationExpression { Operation: ValueOperation.Subtract, Type: "int64_t", Arguments: [var left, var right] } => IsZero(right) && BoundedIndex(left),
        _ => false
    };
    private static bool IsZero(Expression expression) => Unwrap(expression) is ConstantExpression { Value: 0 };
    private static Expression Unwrap(Expression expression) => expression is CapturedExpression captured ? Unwrap(captured.Value) : expression;
}
