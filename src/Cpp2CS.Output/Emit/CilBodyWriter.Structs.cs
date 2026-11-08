using Cpp2CS.Ir;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

internal sealed partial class CilBodyWriter
{
    private void Compose(ComposedValue value)
    {
        var local = Temp(value.Type);
        il.Emit(OpCodes.Ldloca, local);
        il.Emit(OpCodes.Initobj, TypeReference(value.Type));
        foreach (var (path, leaf) in value.Leaves)
        {
            il.Emit(OpCodes.Ldloca, local);
            for (var i = 0; i + 1 < path.Count; i++) il.Emit(OpCodes.Ldflda, FieldReference(path[i]));
            Value(leaf);
            il.Emit(OpCodes.Stfld, FieldReference(path[^1]));
        }
        il.Emit(OpCodes.Ldloc, local);
    }

    private void MathCall(UnaryValue value)
    {
        var single = value.Width == 32;
        Floating(value.Operand);
        if (value.Op == UnOp.FAbs)
        {
            var abs = types.CorlibMethod("System.Math", "Abs", single ? types.Single : types.Double) ?? throw new NotSupportedException("核心库缺少 Math.Abs");
            il.Emit(OpCodes.Call, MethodReference(abs));
            return;
        }
        if (single) il.Emit(OpCodes.Conv_R8);
        var name = CilOperators.Math(value.Op) ?? throw new NotSupportedException(value.Op.ToString());
        var function = types.CorlibMethod("System.Math", name, types.Double) ?? throw new NotSupportedException($"核心库缺少 Math.{name}(double)");
        il.Emit(OpCodes.Call, MethodReference(function));
        if (single) il.Emit(OpCodes.Conv_R4);
    }

    private void Address(ManagedValue value)
    {
        switch (value)
        {
            case ArgumentValue a when a.Index >= 0: il.Emit(OpCodes.Ldarga, destination.Parameters[a.Index]); break;
            case LocalValue l: il.Emit(OpCodes.Ldloca, Local(l)); break;
            case IndirectValue indirect: Value(indirect.Address); break;
            case FieldValue f:
                if (types.Kind(f.Receiver.Type) == TypeKind.Struct) Address(f.Receiver);
                else Value(f.Receiver);
                il.Emit(OpCodes.Ldflda, FieldReference(f.Field));
                break;
            case StaticFieldValue s: il.Emit(OpCodes.Ldsflda, FieldReference(s.Field)); break;
            case ArrayElementValue element:
                Value(element.Array); ElementIndex(element.Index); il.Emit(OpCodes.Ldelema, TypeReference(element.Type)); break;
            case MultiArrayElementValue element:
                Value(element.Array); foreach (var index in element.Indices) Value(index);
                il.Emit(OpCodes.Call, ArrayMethod((ArrayRef)element.Array.Type, "Address")); break;
            default: throw new NotSupportedException($"没有可取地址的存储位置：{value}");
        }
    }
}
