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
                else if (ManagedTypes.IsNativePointer(c.Type) || c.Type is ByRefRef)
                {
                    il.Emit(OpCodes.Ldc_I4_0); il.Emit(OpCodes.Conv_U);
                }
                // 非规范的 NaN 以整数位型输出再重解释，保留载荷。规范的静默 NaN（IL2CPP 对 float.NaN / double.NaN 的翻译，符号位不定）直接作为 NaN 常量，
                // 反编译为 float.NaN：NaN 的符号与载荷只有按位查看时才可区分
                else if (BitConversions.ConstantNeedsBitcast(types, c))
                {
                    if (c.Width == 32) il.Emit(OpCodes.Ldc_I4, unchecked((int)c.Bits));
                    else il.Emit(OpCodes.Ldc_I8, unchecked((long)c.Bits));
                    Reinterpret(types.Integer(c.Width, false), c.Type);
                }
                else if (types.Kind(c.Type) == TypeKind.Float) il.Emit(OpCodes.Ldc_R4, BitConverter.Int32BitsToSingle(unchecked((int)c.Bits)));
                else if (types.Kind(c.Type) == TypeKind.Double) il.Emit(OpCodes.Ldc_R8, BitConverter.Int64BitsToDouble(unchecked((long)c.Bits)));
                else if (c.Width == 64) il.Emit(OpCodes.Ldc_I8, unchecked((long)c.Bits));
                else il.Emit(OpCodes.Ldc_I4, unchecked((int)c.Bits));
                break;
            case StringValue text: il.Emit(OpCodes.Ldstr, text.Text); break;
            case TypeHandleValue handle: il.Emit(OpCodes.Ldtoken, TypeReference(handle.Target)); break;
            case SizeOfValue size: il.Emit(OpCodes.Sizeof, TypeReference(size.Target)); break;
            case FieldHandleValue handle: il.Emit(OpCodes.Ldtoken, FieldReference(handle.Field)); break;
            case StaticCallValue call:
                var factory = Instruction.Create(OpCodes.Call, MethodReference(call.Method));
                il.Append(factory);
                if (call.Inlined) InlineCalls.Add(factory, call.Method);
                break;
            case MethodHandleValue handle: il.Emit(OpCodes.Ldtoken, MethodReference(handle.Method)); break;
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
            case NewMultiArrayValue array:
                foreach (var length in array.Lengths) Value(length);
                il.Emit(OpCodes.Newobj, ArrayMethod(array.ArrayType, ".ctor")); break;
            // ldlen 只用于一维向量；其他数组经 System.Array 的实例方法取总长度。
            case ArrayLengthValue { Array.Type: ArrayRef { IsVector: false } } length:
                Value(length.Array); il.Emit(OpCodes.Callvirt, ArrayInstanceMethod("get_Length", 0)); break;
            case ArrayLengthValue length:
                Value(length.Array); il.Emit(OpCodes.Ldlen); il.Emit(OpCodes.Conv_U4); break;
            case ArrayBoundValue bound:
                Value(bound.Array); il.Emit(OpCodes.Ldc_I4, bound.Dimension);
                il.Emit(OpCodes.Callvirt, ArrayInstanceMethod(bound.Lower ? "GetLowerBound" : "GetLength", 1)); break;
            case MultiArrayElementValue element:
                Value(element.Array); foreach (var index in element.Indices) Value(index);
                il.Emit(OpCodes.Call, ArrayMethod((ArrayRef)element.Array.Type, "Get")); break;
            case StringLengthValue length:
                Value(length.String);
                var stringLength = ((DefinitionRef)types.String).Definition.Methods.Single(m => m.Name == "get_Length" && !m.IsStatic && m.Parameters.Count == 0);
                il.Emit(OpCodes.Callvirt, MethodReference(new MethodRef(stringLength, [], [])));
                break;
            case ArrayElementValue element:
                Value(element.Array); ElementIndex(element.Index); il.Emit(OpCodes.Ldelem_Any, TypeReference(element.Type)); break;
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
                    // 访问器已证明等于这次字段读取，直接在变量上调用，不需要副本。
                    if (f.Receiver is LocalValue or ArgumentValue { Index: >= 0 } && f.Receiver.Type is not ByRefRef)
                    {
                        Address(f.Receiver);
                        AccessorCall(structGetter);
                        break;
                    }
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
            case UnaryValue math when CilOperators.Math(math.Op) is not null:
                MathCall(math); break;
            case UnaryValue u:
                if (u.Op == UnaryOperator.FloatNegate) Floating(u.Operand); else Integer(u.Operand, false);
                il.Emit(CilOperators.Unary(u.Op) ?? throw new NotSupportedException(u.Op.ToString()));
                Normalize(u); break;
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
        if (types.Kind(b.Type) is TypeKind.Float or TypeKind.Double) { Floating(b.Left); Floating(b.Right); }
        else
        {
            Integer(b.Left, b.Op is BinaryOperator.ShiftRightSigned or BinaryOperator.SignedDivide or BinaryOperator.SignedRemainder);
            Integer(b.Right, b.Op is BinaryOperator.SignedDivide or BinaryOperator.SignedRemainder);
            if (b.Op is BinaryOperator.ShiftLeft or BinaryOperator.ShiftRightUnsigned or BinaryOperator.ShiftRightSigned)
            {
                // 移位量按值的位宽取模，避免超出 CIL 移位范围
                il.Emit(OpCodes.Conv_I4); il.Emit(OpCodes.Ldc_I4, b.Width - 1); il.Emit(OpCodes.And);
            }
        }
        il.Emit(CilOperators.Binary(b.Op) ?? throw new NotSupportedException(b.Op.ToString()));
        Normalize(b);
    }

    private void Conversion(ConversionValue c)
    {
        switch (c.Kind)
        {
            case ConversionKind.Bitcast:
                Value(c.Operand); Reinterpret(c.Operand.Type, c.Type); break;
            case ConversionKind.SignExtend:
                Integer(c.Operand, true);
                if (ManagedTypes.IsNativePointer(c.Type)) il.Emit(OpCodes.Conv_I); else IntegerWidth(c.Width, true);
                break;
            case ConversionKind.ZeroExtend or ConversionKind.Truncate:
                Integer(c.Operand, false);
                if (ManagedTypes.IsNativePointer(c.Type)) il.Emit(OpCodes.Conv_U); else IntegerWidth(c.Width, false);
                break;
            case ConversionKind.SignedIntegerToFloat or ConversionKind.UnsignedIntegerToFloat:
                Integer(c.Operand, c.Kind == ConversionKind.SignedIntegerToFloat);
                if (c.Kind == ConversionKind.UnsignedIntegerToFloat) il.Emit(OpCodes.Conv_R_Un);
                il.Emit(c.Width == 32 ? OpCodes.Conv_R4 : OpCodes.Conv_R8); break;
            case ConversionKind.FloatToFloat:
                Floating(c.Operand); il.Emit(c.Width == 32 ? OpCodes.Conv_R4 : OpCodes.Conv_R8); break;
            case ConversionKind.FloatToSignedInteger or ConversionKind.FloatToUnsignedInteger:
                Floating(c.Operand);
                IntegerWidth(c.Width, c.Kind == ConversionKind.FloatToSignedInteger); break;
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
        if (c.Condition is ComparisonKind.FloatOrdered or ComparisonKind.FloatUnordered or ComparisonKind.FloatNotEqual or ComparisonKind.FloatUnorderedOrEqual)
        {
            // 两个操作数只求值一次；无序比较在任一操作数为 NaN 时成立。
            var left = Temp(c.Left.Width == 32 ? types.Single : types.Double);
            var right = Temp(c.Right.Width == 32 ? types.Single : types.Double);
            Floating(c.Left); il.Emit(OpCodes.Stloc, left);
            Floating(c.Right); il.Emit(OpCodes.Stloc, right);
            il.Emit(OpCodes.Ldloc, left); il.Emit(OpCodes.Ldloc, right);
            il.Emit(c.Condition is ComparisonKind.FloatNotEqual or ComparisonKind.FloatUnorderedOrEqual ? OpCodes.Clt : OpCodes.Clt_Un);
            il.Emit(OpCodes.Ldloc, left); il.Emit(OpCodes.Ldloc, right);
            il.Emit(c.Condition is ComparisonKind.FloatNotEqual or ComparisonKind.FloatUnorderedOrEqual ? OpCodes.Cgt : OpCodes.Cgt_Un);
            il.Emit(c.Condition is ComparisonKind.FloatNotEqual or ComparisonKind.FloatUnorderedOrEqual ? OpCodes.Or : OpCodes.And);
            if (c.Condition is ComparisonKind.FloatOrdered or ComparisonKind.FloatUnorderedOrEqual) Invert();
            return;
        }
        var floating = c.Condition is ComparisonKind.FloatEqual or ComparisonKind.FloatUnorderedOrNotEqual or ComparisonKind.FloatLess or ComparisonKind.FloatLessOrEqual or ComparisonKind.FloatGreater or ComparisonKind.FloatGreaterOrEqual or ComparisonKind.FloatUnorderedOrLess or ComparisonKind.FloatUnorderedOrLessOrEqual or ComparisonKind.FloatUnorderedOrGreater or ComparisonKind.FloatUnorderedOrGreaterOrEqual;
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
            var signed = c.Condition is ComparisonKind.SignedLess or ComparisonKind.SignedLessOrEqual or ComparisonKind.SignedGreater or ComparisonKind.SignedGreaterOrEqual;
            void Operand(ManagedValue value)
            {
                // 32 位整数已在 int32 栈上；比较符号由 clt/cgt 指令决定。反编译器追踪状态局部时不认它上面的转换。
                if (value.Width == 32 && types.Kind(value.Type) == TypeKind.Int && (c.Condition is ComparisonKind.Equal or ComparisonKind.NotEqual
                    || (signed || policy == EmissionPolicy.Source) && types.Bits(value.Type) == 32)) Value(value);
                else Integer(value, signed);
            }
            Operand(c.Left); Operand(c.Right);
        }
        il.Emit(c.Condition switch
        {
            ComparisonKind.Equal or ComparisonKind.NotEqual or ComparisonKind.FloatEqual or ComparisonKind.FloatUnorderedOrNotEqual => OpCodes.Ceq,
            ComparisonKind.SignedLess or ComparisonKind.SignedGreaterOrEqual or ComparisonKind.FloatLess or ComparisonKind.FloatUnorderedOrGreaterOrEqual => OpCodes.Clt,
            ComparisonKind.SignedGreater or ComparisonKind.SignedLessOrEqual or ComparisonKind.FloatGreater or ComparisonKind.FloatUnorderedOrLessOrEqual => OpCodes.Cgt,
            ComparisonKind.UnsignedLess or ComparisonKind.UnsignedGreaterOrEqual or ComparisonKind.FloatUnorderedOrLess or ComparisonKind.FloatGreaterOrEqual => OpCodes.Clt_Un,
            ComparisonKind.UnsignedGreater or ComparisonKind.UnsignedLessOrEqual or ComparisonKind.FloatUnorderedOrGreater or ComparisonKind.FloatLessOrEqual => OpCodes.Cgt_Un,
            _ => throw new NotSupportedException(c.Condition.ToString()),
        });
        if (c.Condition is ComparisonKind.NotEqual or ComparisonKind.SignedLessOrEqual or ComparisonKind.SignedGreaterOrEqual or ComparisonKind.UnsignedLessOrEqual or ComparisonKind.UnsignedGreaterOrEqual or ComparisonKind.FloatUnorderedOrNotEqual or ComparisonKind.FloatLessOrEqual or ComparisonKind.FloatGreaterOrEqual or ComparisonKind.FloatUnorderedOrLessOrEqual or ComparisonKind.FloatUnorderedOrGreaterOrEqual) Invert();
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
        if ((ManagedTypes.IsNativePointer(from) || from is ByRefRef) && ManagedTypes.IsNativePointer(to))
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

    /// <summary>多维数组类型由运行时提供的方法（ECMA-335 II.14.2）：.ctor 与 Get、Address 取各维 int32 下标，Set 再取元素值。</summary>
    private MethodReference ArrayMethod(ArrayRef array, string name)
    {
        var module = destination.Module;
        var element = TypeReference(array.Element);
        TypeReference returned = name switch { ".ctor" or "Set" => module.TypeSystem.Void, "Address" => new ByReferenceType(element), _ => element };
        var method = new MethodReference(name, returned, TypeReference(array)) { HasThis = true };
        for (var i = 0; i < array.Rank; i++) method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
        if (name == "Set") method.Parameters.Add(new ParameterDefinition(element));
        return method;
    }

    private MethodReference ArrayInstanceMethod(string name, int parameters)
    {
        var array = types.CorlibDefinition("System.Array") ?? throw new InvalidOperationException("corlib 没有 System.Array");
        return MethodReference(new MethodRef(array.Methods.Single(m => m.Name == name && !m.IsStatic && m.Parameters.Count == parameters), [], []));
    }
}
