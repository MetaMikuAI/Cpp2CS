using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    // 原生整数与非托管指针只在类型化位置和整数位型之间转换。
    private ManagedValue NativeIntegerBits(ManagedValue value)
    {
        if (value is ConversionValue { Kind: ConversionKind.Bitcast } cast
            && IntegerType(cast.Operand.Type) && cast.Operand.Width == types.PointerSize * 8) return cast.Operand;
        return new ConversionValue(ConversionKind.Bitcast, value,
            types.Integer(types.PointerSize * 8, ManagedTypes.IsSigned(value.Type)), types.PointerSize * 8);
    }

    private ManagedValue NativeBits(ManagedValue value, TypeRef type)
    {
        if (ReferenceType(value.Type))
        {
            Fail<object>(LoweringFailureKind.UnsupportedType, "托管引用不能流入原生整数或非托管指针位置", code: "lowering.NativeInt.Reference");
            return value;
        }
        if (!ManagedTypes.IsNativePointer(value.Type) && !IntegerType(value.Type) && !IsFloat(value.Type))
        {
            Fail<object>(LoweringFailureKind.UnsupportedType, "值缺少原生整数或非托管指针所需的标量位型", code: "lowering.NativeInt.Type");
            return value;
        }
        if (Equals(value.Type, type)) return value;
        if (value is ConversionValue { Kind: ConversionKind.Bitcast } cast
            && ManagedTypes.IsNativePointer(cast.Operand.Type) && cast.Width == types.PointerSize * 8)
            return NativeBits(cast.Operand, type);
        if (!ManagedTypes.IsNativePointer(value.Type)) value = Convert(value, types.PointerSize * 8);
        return new ConversionValue(ConversionKind.Bitcast, value, type, types.PointerSize * 8);
    }
}
