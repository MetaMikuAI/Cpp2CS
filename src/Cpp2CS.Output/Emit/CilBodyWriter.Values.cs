using Cpp2CS.Ir;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>值的 CIL 写法：每种值一处。求值栈上的整数只有 32 位与 64 位，运算之后按值的位宽与符号规范化。</summary>
internal sealed partial class CilBodyWriter
{
    private void Value(ManagedValue value)
    {
        switch (value)
        {
            case ArgumentValue a:
                if (a.Index == -1) il.Emit(OpCodes.Ldarg_0);
                else il.Emit(OpCodes.Ldarg, destination.Parameters[a.Index]);
                break;
            case LocalValue l: il.Emit(OpCodes.Ldloc, Local(l)); break;
            case AsyncResultValue result:
                if (result.Value is { } completed)
                {
                    // builder 内联后可能只剩寄存器整数类型；返回标记保留任务声明的符号与枚举类型。
                    var completedType = result.Type is DefinitionRef { Arguments: [var declared] }
                        && types.Kind(declared) == TypeKind.Int && types.Kind(completed.Type) == TypeKind.Int
                        && types.Bits(completed.Type) == types.Bits(declared)
                        ? declared : completed.Type;
                    Value(completed);
                    il.Emit(OpCodes.Call, Generic(Awaits().Result, result.Type, completedType));
                }
                else if (ManagedTypes.IsVoid(result.Type)) il.Emit(OpCodes.Call, Awaits().CompletedVoid);
                else il.Emit(OpCodes.Call, Generic(Awaits().Completed, result.Type));
                break;
            case HoleValue hole:
                il.Emit(OpCodes.Ldc_I8, unchecked((long)statementAddress));
                il.Emit(OpCodes.Call, new GenericInstanceMethod(Unrecovered().Value) { GenericArguments = { TypeReference(hole.Type) } });
                break;
            case ConstantValue c:
                if (c.Type is GenericParameterRef { IsReferenceConstrained: false })
                {
                    var zero = Temp(c.Type);
                    il.Emit(OpCodes.Ldloca, zero); il.Emit(OpCodes.Initobj, TypeReference(c.Type)); il.Emit(OpCodes.Ldloc, zero);
                }
                else if (ManagedTypes.IsReferenceType(c.Type)) il.Emit(OpCodes.Ldnull);
                else if (ManagedTypes.IsNativePointer(c.Type))
                {
                    il.Emit(OpCodes.Ldc_I4_0); il.Emit(OpCodes.Conv_U);
                }
                // 非规范的 NaN 以整数位型输出再重解释，保留载荷。规范的静默 NaN（IL2CPP 对 float.NaN / double.NaN 的翻译，符号位不定）直接作为 NaN 常量，
                // 反编译为 float.NaN：NaN 的符号与载荷只有按位查看时才可区分
                else if (types.Kind(c.Type) == TypeKind.Float && (c.Bits & 0x7f800000) == 0x7f800000 && (c.Bits & 0x7fffff) != 0 && (c.Bits & 0x7fffffff) != 0x7fc00000)
                {
                    il.Emit(OpCodes.Ldc_I4, unchecked((int)c.Bits)); Reinterpret(types.UInt32, c.Type);
                }
                else if (types.Kind(c.Type) == TypeKind.Double && (c.Bits & 0x7ff0000000000000) == 0x7ff0000000000000 && (c.Bits & 0xfffffffffffff) != 0
                    && (c.Bits & 0x7fffffffffffffff) != 0x7ff8000000000000)
                {
                    il.Emit(OpCodes.Ldc_I8, unchecked((long)c.Bits)); Reinterpret(types.UInt64, c.Type);
                }
                else if (types.Kind(c.Type) == TypeKind.Float) il.Emit(OpCodes.Ldc_R4, BitConverter.Int32BitsToSingle(unchecked((int)c.Bits)));
                else if (types.Kind(c.Type) == TypeKind.Double) il.Emit(OpCodes.Ldc_R8, BitConverter.Int64BitsToDouble(unchecked((long)c.Bits)));
                else if (c.Width == 64) il.Emit(OpCodes.Ldc_I8, unchecked((long)c.Bits));
                else il.Emit(OpCodes.Ldc_I4, unchecked((int)c.Bits));
                break;
            case StringValue text: il.Emit(OpCodes.Ldstr, text.Text); break;
            case TypeHandleValue handle: il.Emit(OpCodes.Ldtoken, TypeReference(handle.Target)); break;
            case BoxValue box: Value(box.Operand); il.Emit(OpCodes.Box, TypeReference(box.Boxed)); break;
            case UnboxAddressValue unbox: Value(unbox.Operand); il.Emit(OpCodes.Unbox, TypeReference(unbox.Target)); break;
            case UnboxValue unbox: Value(unbox.Operand); il.Emit(OpCodes.Unbox_Any, TypeReference(unbox.Target)); break;
            case IsInstValue test:
                Value(test.Operand);
                if (test.Operand.Type is GenericParameterRef { IsReferenceConstrained: false }) il.Emit(OpCodes.Box, TypeReference(test.Operand.Type));
                il.Emit(OpCodes.Isinst, TypeReference(test.Target));
                // isinst 的结果是对象引用；开放泛型局部需要恢复为 !T 栈类型。
                if (test.BoxedType is null && test.Target is GenericParameterRef { IsReferenceConstrained: false }) il.Emit(OpCodes.Unbox_Any, TypeReference(test.Target));
                break;
            case CheckedCastValue cast:
                Value(cast.Operand); il.Emit(OpCodes.Castclass, TypeReference(cast.Target)); break;
            case NewObjectValue created:
                {
                    foreach (var argument in created.Arguments) Value(argument);
                    var newobj = Instruction.Create(OpCodes.Newobj, MethodReference(created.Constructor));
                    il.Append(newobj);
                    if (created.Transparent) InlineCalls.Add(newobj, created.Constructor);
                    break;
                }
            case DelegateValue delegated:
                EmitDelegate(delegated); break;
            case NewArrayValue array:
                Value(array.Length); il.Emit(OpCodes.Newarr, TypeReference(array.ArrayType.Element)); break;
            case ArrayLengthValue length:
                Value(length.Array); il.Emit(OpCodes.Ldlen); il.Emit(OpCodes.Conv_U4); break;
            case ArrayElementValue element:
                Value(element.Array); Value(element.Index); il.Emit(OpCodes.Ldelem_Any, TypeReference(element.Type)); break;
            case AddressValue a: Address(a.Target); break;
            case PinnedArrayValue pinned:
                PinArray(pinned); break;
            case PointerOffsetValue pointer:
                Value(pointer.Pointer); Value(pointer.Offset); il.Emit(OpCodes.Conv_I); il.Emit(OpCodes.Add); break;
            // 读取存储位置上的整个结构体：直接 ldloc/ldarg/ldfld/ldsfld（不对只读静态字段取址）
            case IndirectValue { Address: AddressValue { Target: LocalValue or FieldValue or StaticFieldValue or ArgumentValue { Index: >= 0 } } location } i
                when location.Target.Type.Equals(i.Type):
                Value(location.Target); break;
            case IndirectValue i: Value(i.Address); il.Emit(OpCodes.Ldobj, TypeReference(i.Type)); break;
            case ComposedValue c: Compose(c); break;
            case FieldValue f:
                // 枚举的 value__ 是整个值的底层表示；以 ldobj 读取，避免 C# 泄漏不可访问的字段名。
                if (f.Field.Field is { Owner.IsEnum: true, Name: "value__" } && f.Receiver.Type is ByRefRef enumReference
                    && enumReference.Element.Equals(f.Field.DeclaringType))
                { Value(f.Receiver); il.Emit(OpCodes.Ldobj, TypeReference(enumReference.Element)); break; }
                // 值类型的访问器是实例方法：this 是该值的地址（ldloca/ldflda），不能先读出值。
                if (f.Accessor is { Method.Method.Owner.IsValueType: true } structGetter)
                {
                    Value(f.Receiver);
                    if (f.Receiver.Type is not ByRefRef)
                    {
                        var copy = Temp(f.Receiver.Type);
                        il.Emit(OpCodes.Stloc, copy);
                        il.Emit(OpCodes.Ldloca, copy);
                    }
                    AccessorCall(structGetter);
                    break;
                }
                Value(f.Receiver is AddressValue address ? address.Target : f.Receiver);
                if (f.Accessor is { } getter) AccessorCall(getter); else il.Emit(OpCodes.Ldfld, FieldReference(f.Field)); break;
            case StaticFieldValue f:
                if (f.Accessor is { } staticGetter) AccessorCall(staticGetter); else il.Emit(OpCodes.Ldsfld, FieldReference(f.Field)); break;
            case BinaryValue b: Binary(b); break;
            // 浮点的绝对值、平方根与取整写成 System.Math 的调用（float 经 double 计算：这些运算对 float 的值结果精确，转回 float 不再舍入）
            case UnaryValue { Op: UnOp.FAbs or UnOp.FSqrt or UnOp.FFloor or UnOp.FCeil or UnOp.FTrunc or UnOp.FRoundEven } math:
                MathCall(math); break;
            case UnaryValue u:
                if (u.Op == UnOp.FNeg) Floating(u.Operand); else Integer(u.Operand, false);
                il.Emit(u.Op == UnOp.Not ? OpCodes.Not : OpCodes.Neg);
                Normalize(u); break;
            case ConversionValue { Type: GenericParameterRef { NativeScalar: not null } } copy:
                Value(copy.Operand); break;
            case ConversionValue c: Conversion(c); break;
            case ComparisonValue c: Comparison(c); break;
            case ChoiceValue c:
                var no = Instruction.Create(OpCodes.Nop);
                var end = Instruction.Create(OpCodes.Nop);
                Value(c.Condition); il.Emit(OpCodes.Brfalse, no);
                Value(c.True); il.Emit(OpCodes.Br, end);
                il.Append(no); Value(c.False); il.Append(end); break;
            case BooleanValue b:
                var shortCircuit = Instruction.Create(OpCodes.Nop);
                var done = Instruction.Create(OpCodes.Nop);
                Value(b.Left); il.Emit(b.IsAnd ? OpCodes.Brfalse : OpCodes.Brtrue, shortCircuit);
                Value(b.Right); il.Emit(OpCodes.Br, done);
                il.Append(shortCircuit); il.Emit(OpCodes.Ldc_I4, b.IsAnd ? 0 : 1); il.Append(done); break;
            case NegatedValue n: Value(n.Operand); Invert(); break;
            default: throw new NotSupportedException(value.ToString());
        }
    }

    private void Binary(BinaryValue b)
    {
        if (b.Op is BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber or BinOp.SDiv or BinOp.UDiv)
        {
            if (b.Op is BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber) { Floating(b.Left); Floating(b.Right); }
            else { Integer(b.Left, b.Op == BinOp.SDiv); Integer(b.Right, b.Op == BinOp.SDiv); }
            NativeArithmetic.Emit(il, b.Op, b.Width, name => TypeReference(types.Corlib(name)), name => MethodReference(
                types.CorlibMethod("System.BitConverter", name, name switch
                {
                    "SingleToInt32Bits" => types.Single,
                    "DoubleToInt64Bits" => types.Double,
                    "Int32BitsToSingle" => types.Int32,
                    _ => types.Int64,
                }) ?? throw new NotSupportedException($"核心库缺少 BitConverter.{name}")),
                rightConstant: b.Right is ConstantValue constant ? constant.Bits : null);
            Normalize(b);
            return;
        }
        if (types.Kind(b.Type) is TypeKind.Float or TypeKind.Double) { Floating(b.Left); Floating(b.Right); }
        else
        {
            Integer(b.Left, b.Op == BinOp.AShr);
            Integer(b.Right, false);
            if (b.Op is BinOp.Shl or BinOp.LShr or BinOp.AShr)
            {
                // ARM64 的移位量按位宽取模；CIL 的移位量超出位宽时结果未定义
                il.Emit(OpCodes.Conv_I4); il.Emit(OpCodes.Ldc_I4, b.Width - 1); il.Emit(OpCodes.And);
            }
        }
        il.Emit(b.Op switch
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
            _ => throw new NotSupportedException(b.Op.ToString()),
        });
        Normalize(b);
    }

    private void Conversion(ConversionValue c)
    {
        switch (c.Kind)
        {
            case ConvKind.Bitcast:
                Value(c.Operand); Reinterpret(c.Operand.Type, c.Type); break;
            case ConvKind.SignExtend:
                Integer(c.Operand, true); IntegerWidth(c.Width, true); break;
            case ConvKind.ZeroExtend or ConvKind.Truncate:
                Integer(c.Operand, false); IntegerWidth(c.Width, false); break;
            case ConvKind.SIntToFloat or ConvKind.UIntToFloat:
                Integer(c.Operand, c.Kind == ConvKind.SIntToFloat);
                if (c.Kind == ConvKind.UIntToFloat) il.Emit(OpCodes.Conv_R_Un);
                il.Emit(c.Width == 32 ? OpCodes.Conv_R4 : OpCodes.Conv_R8); break;
            case ConvKind.FloatToFloat:
                Floating(c.Operand); il.Emit(c.Width == 32 ? OpCodes.Conv_R4 : OpCodes.Conv_R8); break;
            case ConvKind.FloatToSInt or ConvKind.FloatToUInt:
                Floating(c.Operand);
                NativeArithmetic.FloatToInteger(il, c.Operand.Width, c.Width, c.Kind == ConvKind.FloatToSInt,
                    name => TypeReference(types.Corlib(name))); break;
            default: throw new NotSupportedException(c.Kind.ToString());
        }
    }

    private void PinArray(PinnedArrayValue pinned)
    {
        var local = pinnedArrays[pinned];
        var pointer = Temp(pinned.Type);
        var empty = Instruction.Create(OpCodes.Ldc_I4_0);
        var address = Instruction.Create(OpCodes.Ldloc, local);
        var done = Instruction.Create(OpCodes.Nop);
        Value(pinned.Array); il.Emit(OpCodes.Dup); il.Emit(OpCodes.Stloc, local); il.Emit(OpCodes.Brfalse, empty);
        il.Emit(OpCodes.Ldloc, local); il.Emit(OpCodes.Ldlen); il.Emit(OpCodes.Conv_I4); il.Emit(OpCodes.Brtrue, address);
        il.Append(empty); il.Emit(OpCodes.Conv_U); il.Emit(OpCodes.Stloc, pointer); il.Emit(OpCodes.Br, done);
        il.Append(address); il.Emit(OpCodes.Ldc_I4_0); il.Emit(OpCodes.Ldelema, TypeReference(pinned.ArrayType.Element));
        il.Emit(OpCodes.Conv_U); il.Emit(OpCodes.Stloc, pointer);
        il.Append(done); il.Emit(OpCodes.Ldloc, pointer);
    }

    private void ClearPinnedArrays()
    {
        foreach (var local in pinnedArrays.Values) { il.Emit(OpCodes.Ldnull); il.Emit(OpCodes.Stloc, local); }
    }

    private void Comparison(ComparisonValue c)
    {
        if (c.Condition is Cond.FOrdered or Cond.FUnordered or Cond.FNe)
        {
            // 两个操作数只求值一次；无序比较在任一操作数为 NaN 时成立。
            var left = Temp(c.Left.Width == 32 ? types.Single : types.Double);
            var right = Temp(c.Right.Width == 32 ? types.Single : types.Double);
            Floating(c.Left); il.Emit(OpCodes.Stloc, left);
            Floating(c.Right); il.Emit(OpCodes.Stloc, right);
            il.Emit(OpCodes.Ldloc, left); il.Emit(OpCodes.Ldloc, right);
            il.Emit(c.Condition == Cond.FNe ? OpCodes.Clt : OpCodes.Clt_Un);
            il.Emit(OpCodes.Ldloc, left); il.Emit(OpCodes.Ldloc, right);
            il.Emit(c.Condition == Cond.FNe ? OpCodes.Cgt : OpCodes.Cgt_Un);
            il.Emit(c.Condition == Cond.FNe ? OpCodes.Or : OpCodes.And);
            if (c.Condition == Cond.FOrdered) Invert();
            return;
        }
        var floating = c.Condition is Cond.FEq or Cond.FUne or Cond.FLt or Cond.FLe or Cond.FGt or Cond.FGe or Cond.FUlt or Cond.FUle or Cond.FUgt or Cond.FUge;
        if (ManagedTypes.IsReferenceType(c.Left.Type) || ManagedTypes.IsReferenceType(c.Right.Type))
        {
            void Reference(ManagedValue operand)
            {
                if (operand is ConstantValue { Bits: 0 }) { il.Emit(OpCodes.Ldnull); return; }
                Value(operand);
                if (operand.Type is GenericParameterRef { IsReferenceConstrained: false }) il.Emit(OpCodes.Box, TypeReference(operand.Type));
            }
            Reference(c.Left); Reference(c.Right);
        }
        else if (floating) { Floating(c.Left); Floating(c.Right); }
        else
        {
            var signed = c.Condition is Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge;
            void Operand(ManagedValue value)
            {
                // 32 位整数已在 int32 栈上；比较符号由 clt/cgt 指令决定。
                if (value.Width == 32 && types.Kind(value.Type) == TypeKind.Int && (c.Condition is Cond.Eq or Cond.Ne
                    || policy == EmissionPolicy.Source && types.Bits(value.Type) == 32)) Value(value);
                else Integer(value, signed);
            }
            Operand(c.Left); Operand(c.Right);
        }
        il.Emit(c.Condition switch
        {
            Cond.Eq or Cond.Ne or Cond.FEq or Cond.FUne => OpCodes.Ceq,
            Cond.Slt or Cond.Sge or Cond.FLt or Cond.FUge => OpCodes.Clt,
            Cond.Sgt or Cond.Sle or Cond.FGt or Cond.FUle => OpCodes.Cgt,
            Cond.Ult or Cond.Uge or Cond.FUlt or Cond.FGe => OpCodes.Clt_Un,
            Cond.Ugt or Cond.Ule or Cond.FUgt or Cond.FLe => OpCodes.Cgt_Un,
            _ => throw new NotSupportedException(c.Condition.ToString()),
        });
        if (c.Condition is Cond.Ne or Cond.Sle or Cond.Sge or Cond.Ule or Cond.Uge or Cond.FUne or Cond.FLe or Cond.FGe or Cond.FUle or Cond.FUge) Invert();
    }

    private void Integer(ManagedValue value, bool signed)
    {
        Value(value);
        if (types.Kind(value.Type) is TypeKind.Float or TypeKind.Double) Reinterpret(value.Type, types.Integer(value.Width, signed));
        IntegerWidth(value.Width, signed);
    }

    private void Floating(ManagedValue value)
    {
        Value(value);
        if (types.Kind(value.Type) is not (TypeKind.Float or TypeKind.Double))
            Reinterpret(value.Type, value.Width == 32 ? types.Single : types.Double);
    }

    private void Reinterpret(TypeRef from, TypeRef to)
    {
        if (ManagedTypes.IsNativePointer(from) && ManagedTypes.IsNativePointer(to))
        {
            il.Emit(ManagedTypes.IsSigned(to) ? OpCodes.Conv_I : OpCodes.Conv_U);
            return;
        }
        var fromFloat = types.Kind(from) is TypeKind.Float or TypeKind.Double;
        var toFloat = types.Kind(to) is TypeKind.Float or TypeKind.Double;
        if (fromFloat == toFloat) return;
        il.Emit(OpCodes.Call, MethodReference(BitConversions.Find(types, from, to)
            ?? throw new NotSupportedException($"缺少同宽位重解释: {from} → {to}")));
    }



    private void Normalize(ManagedValue value)
    {
        if (types.Kind(value.Type) is TypeKind.Float or TypeKind.Double) il.Emit(value.Width == 32 ? OpCodes.Conv_R4 : OpCodes.Conv_R8);
        else IntegerWidth(value.Width, ManagedTypes.IsSigned(value.Type));
    }

    private void IntegerWidth(int width, bool signed)
    {
        if (width == 1) { il.Emit(OpCodes.Conv_I4); il.Emit(OpCodes.Ldc_I4_1); il.Emit(OpCodes.And); return; }
        il.Emit((width, signed) switch
        {
            (8, true) => OpCodes.Conv_I1,
            (8, false) => OpCodes.Conv_U1,
            (16, true) => OpCodes.Conv_I2,
            (16, false) => OpCodes.Conv_U2,
            (32, true) => OpCodes.Conv_I4,
            (32, false) => OpCodes.Conv_U4,
            (64, true) => OpCodes.Conv_I8,
            (64, false) => OpCodes.Conv_U8,
            _ => throw new NotSupportedException($"整数宽度 {width}"),
        });
    }

    private void Invert() { il.Emit(OpCodes.Ldc_I4_0); il.Emit(OpCodes.Ceq); }
}
