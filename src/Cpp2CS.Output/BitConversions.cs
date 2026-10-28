using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

internal static class BitConversions
{
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
