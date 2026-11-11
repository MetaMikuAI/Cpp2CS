
namespace Cpp2CS.Output;

public static class BitConversions
{
    /// <summary>非规范 NaN 常量需经位重解释保留载荷；与实际常量写出共用此判据。</summary>
    public static bool ConstantNeedsBitcast(ManagedTypes types, ConstantValue value) => types.Kind(value.Type) switch
    {
        TypeKind.Float => (value.Bits & 0x7f800000) == 0x7f800000 && (value.Bits & 0x7fffff) != 0
            && (value.Bits & 0x7fffffff) != 0x7fc00000,
        TypeKind.Double => (value.Bits & 0x7ff0000000000000) == 0x7ff0000000000000 && (value.Bits & 0xfffffffffffff) != 0
            && (value.Bits & 0x7fffffffffffffff) != 0x7ff8000000000000,
        _ => false,
    };

    /// <summary>同宽位重解释使用 BCL 契约，不通过不同类型的托管地址读取。</summary>
    public static MethodRef? Find(ManagedTypes types, TypeRef from, TypeRef to)
    {
        var width = types.Bits(from);
        if (width != types.Bits(to) || width is not (32 or 64)) return null;
        var fromKind = types.Kind(from);
        var toKind = types.Kind(to);
        var name = (fromKind, toKind) switch
        {
            (TypeKind.Float, TypeKind.Int) => "SingleToInt32Bits",
            (TypeKind.Double, TypeKind.Int) => "DoubleToInt64Bits",
            (TypeKind.Int, TypeKind.Float) => "Int32BitsToSingle",
            (TypeKind.Int, TypeKind.Double) => "Int64BitsToDouble",
            _ => null,
        };
        if (name is null) return null;
        var parameter = fromKind == TypeKind.Int ? types.Integer(width, true) : from;
        var expected = toKind == TypeKind.Int ? types.Integer(width, true) : to;
        return types.CorlibMethod("System.BitConverter", name, parameter) is { Method.IsStatic: true } method
            && method.Method.ReturnType.Equals(expected) ? method : null;
    }
}
