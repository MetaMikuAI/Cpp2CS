using Cpp2CS.Ir;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

public sealed partial class BodyEmitter
{
    private string? ReadonlyWriteProblem(ManagedValue value)
    {
        if (value is AddressValue a) return ReadonlyWriteProblem(a.Target);
        if (value is IndirectValue indirect) return ReadonlyWriteProblem(indirect.Address);
        if (value is not FieldValue field || IgnoreAccess) return null;
        if ((field.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(methodContext.Method.Name == ".ctor" && methodContext.Method.Owner == field.Field.Field.Owner))
            return $"只读实例字段 不能在所属类型构造函数之外取得可写地址：{field.Field}";
        if (field.Receiver is AddressValue address) return ReadonlyWriteProblem(address.Target);
        return null;
    }

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
        var name = value.Op switch { UnOp.FSqrt => "Sqrt", UnOp.FFloor => "Floor", UnOp.FCeil => "Ceiling", UnOp.FTrunc => "Truncate", _ => "Round" };
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
            case FieldValue f: Value(f.Receiver); il.Emit(OpCodes.Ldflda, FieldReference(f.Field)); break;
            case StaticFieldValue s: il.Emit(OpCodes.Ldsflda, FieldReference(s.Field)); break;
            default: throw new NotSupportedException($"没有可取地址的存储位置：{value}");
        }
    }
}
