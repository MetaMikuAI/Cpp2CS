using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private static int StackWidth(int width) => width <= 32 ? 32 : 64;
    private TypeRef StackType(int width) => width <= 32 ? types.Int32 : types.Int64;
    private static bool IntegerType(TypeRef type) => ManagedTypes.PrimitiveName(ManagedTypes.Underlying(type)) is
        "Boolean" or "Char" or "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64";
    private LoweringFailureKind TypeFailure(TypeRef type) => types.Kind(type) is TypeKind.Float or TypeKind.Double
        ? LoweringFailureKind.FloatingOrVector : LoweringFailureKind.UnsupportedType;
    private ConstantValue Constant(ulong bits, int width) => new(bits, StackType(width), StackWidth(width));
    private ManagedValue Convert(ManagedValue value, int width, bool signed = false)
    {
        value = IntegerBits(value);
        var target = StackWidth(width);
        return value.Width == target ? value : new ConversionValue(signed ? ConversionKind.SignExtend : ConversionKind.ZeroExtend, value, StackType(width), target);
    }
    // 任意位片先按 IL 栈宽度求值，再以掩码截断；不把非标准位宽交给 CIL 转换。
    private ManagedValue Mask(ManagedValue value, int width)
    {
        value = Convert(value, width);
        return width == StackWidth(width) ? value : new BinaryValue(BinaryOperator.And, value,
            Constant((1UL << width) - 1, width), StackType(width), StackWidth(width));
    }
    private ManagedValue Signed(ManagedValue value, int width)
    {
        value = Mask(value, width);
        int shift = StackWidth(width) - width;
        return shift == 0 ? value : Binary(BinaryOperator.ShiftRightSigned,
            Binary(BinaryOperator.ShiftLeft, value, Constant((ulong)shift, 32), StackWidth(width)), Constant((ulong)shift, 32), StackWidth(width));
    }
    private ManagedValue Binary(BinaryOperator op, ManagedValue left, ManagedValue right, int width) =>
        new BinaryValue(op, Convert(left, width), Convert(right, op is BinaryOperator.ShiftLeft or BinaryOperator.ShiftRightSigned or BinaryOperator.ShiftRightUnsigned ? 32 : width), StackType(width), StackWidth(width));

    private ManagedValue? Value(Term term, bool floating = false)
    {
        if (values.TryGetValue(term, out var known)) return known;
        var resolved = context.Get(state.Resolve, term);
        if (!resolved.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.State, "值查询失败", resolved.Why);
        var value = resolved.Value == term ? BuildValue(term, floating) : Value(resolved.Value, floating);
        if (value is not null) values.Add(term, value);
        return value;
    }
    private ManagedValue? BuildValue(Term term, bool floating = false)
    {
        if (term.Identity is RootAtom { Kind: AddressRoot.Frame })
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "帧地址用于普通值或运算", code: "lowering.Frame.Use");
        if (locations is not null && context.Get(locations.Addresses, term).IsSuccess && StaticType(term) is not ByRefRef)
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "托管地址用于运算、比较或普通值", code: "lowering.Address.Use");
        var structurePart = StructPart(term, 0, term.Width);
        if (structurePart is not null || failure is not null) return structurePart;
        if (readValues.TryGetValue(term, out var read)) return ReadValue(read);
        if (callResults.TryGetValue(term, out var callResult))
            return types.Kind(callResult.Method.Concrete(callResult.Method.Method.ReturnType)) == TypeKind.Struct
                ? StructScalarFailure(callResult.Method.Concrete(callResult.Method.Method.ReturnType)) : CallResult(callResult);
        if (objects.TryGetValue(term, out var created)) return ObjectValue(created);
        if (vectorResults.TryGetValue(term, out var vector)) return vector.Local;
        if (runtimeValues.TryGetValue(term, out var runtime)) return runtime;
        if (arguments.TryGetValue(term, out var argument))
            return Opaque(argument.Type) || IsFloat(argument.Type) || ReferenceType(argument.Type) || ManagedTypes.IsNativePointer(argument.Type) ? argument : IntegerType(argument.Type) ? Mask(argument, term.Width)
                : Fail<ManagedValue>(TypeFailure(argument.Type), "使用了非整数形参");
        if (term.Width > 64) return Fail<ManagedValue>(LoweringFailureKind.FloatingOrVector, "项位宽超过整数栈宽度");
        if (term.Identity is ResultAtom { Definition: ReadIdentity readId })
        {
            var resolved = context.Get(state.Read, readId);
            return resolved.IsSuccess ? Value(resolved.Value, floating) : Fail<ManagedValue>(LoweringFailureKind.State, "读取查询失败", resolved.Why);
        }
        if (term.Identity is ResultAtom { Definition: MergeIdentity } or MemoryMerge) return MergeValue(term, floating: floating);
        if (term.Kind == TermKind.Constant) return Constant((ulong)term.ConstantValue!.Value, term.Width);
        if (term.Kind is TermKind.Undefined or TermKind.Unknown)
            return Fail<ManagedValue>(LoweringFailureKind.UndefinedValue, "使用未定义或未知的位", term.Why);
        if (term.Kind == TermKind.Slice) return Part(term.Operands[0], term.SliceLow!.Value, term.Width, floating);
        if (term.Kind == TermKind.Concat)
        {
            ManagedValue result = Constant(0, term.Width); int offset = 0;
            foreach (var part in term.Operands)
            {
                var value = Value(part); if (value is null) return null;
                value = Convert(Mask(value, part.Width), term.Width);
                if (offset != 0) value = Binary(BinaryOperator.ShiftLeft, value, Constant((ulong)offset, 32), term.Width);
                result = Binary(BinaryOperator.Or, result, value, term.Width); offset += part.Width;
            }
            return Mask(result, term.Width);
        }
        if (term.Identity is ResultAtom { Definition: CallIdentity lookup } && interfaceLookups.Contains(lookup))
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedAtom, "接口调用数据没有托管值定义");
        if (term.Identity is ResultAtom { Definition: CallIdentity })
            return Fail<ManagedValue>(LoweringFailureKind.Binding, "使用了调用结果绑定之外的位，ABI 未定义这些高位");
        if (term.Identity is EntryAtom)
            return Fail<ManagedValue>(LoweringFailureKind.Binding, "使用了形参绑定未定义的入口位，包括未指定的槽位高位");
        if (term.Identity is MemoryAtom)
            return Fail<ManagedValue>(LoweringFailureKind.State, "帧读取没有可下降的入口值或写入定义");
        if (term.Operator is CoreOperator core) return Operation(term, core.Operation, floating);
        return Fail<ManagedValue>(LoweringFailureKind.UnsupportedAtom, $"没有托管定义：{term.Identity?.StableText ?? term.Operator?.Name ?? term.Kind.ToString()}");
    }
    /// <summary>使用点所需的位片约束合流局部；不要求被丢弃的槽位高位具有托管定义。</summary>
    private ManagedValue? Part(Term term, int low, int width, bool floating = false)
    {
        if (low == 0 && width == term.Width) return Value(term, floating);
        var structurePart = StructPart(term, low, width);
        if (structurePart is not null || failure is not null) return structurePart;
        var resolved = context.Get(state.Resolve, term);
        if (!resolved.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.State, "位片来源查询失败", resolved.Why);
        if (resolved.Value != term) return Part(resolved.Value, low, width, floating);
        foreach (var pair in callResults)
        {
            var root = pair.Key.Kind == TermKind.Slice ? pair.Key.Operands[0] : pair.Key;
            int start = pair.Key.SliceLow ?? 0;
            if (term == root && low >= start && low + width <= start + pair.Key.Width)
            {
                var type = pair.Value.Method.Concrete(pair.Value.Method.Method.ReturnType);
                if (types.Kind(type) == TypeKind.Struct) return StructScalarFailure(type);
                var result = CallResult(pair.Value);
                return result is null ? null : Slice(result, low - start, width);
            }
        }
        if (term.Identity is ResultAtom { Definition: MergeIdentity } or MemoryMerge)
        {
            // 局部容纳使用位片；完整浮点使用可定型，其他位片按整数保存。
            // 右移反馈不为每个后缀生成另一份合流。
            int end = low + width;
            int storageWidth = Math.Min(term.Width, end <= 8 ? 8 : end <= 16 ? 16 : end <= 32 ? 32 : 64);
            var local = MergeValue(term, 0, storageWidth, floating && low == 0 && width == storageWidth);
            return local is null ? null : low == 0 && width == local.Width ? local : Slice(local, low, width);
        }
        if (term.Kind == TermKind.Slice) return Part(term.Operands[0], low + term.SliceLow!.Value, width, floating);
        foreach (var pair in arguments)
        {
            var root = pair.Key.Kind == TermKind.Slice ? pair.Key.Operands[0] : pair.Key;
            int start = pair.Key.SliceLow ?? 0;
            if (term != root || low < start || low + width > start + pair.Key.Width) continue;
            if (ReferenceType(pair.Value.Type)) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
                "托管引用或地址的部分位片用于普通值或运算", code: "lowering.Address.Use");
            if (!Opaque(pair.Value.Type) && !IntegerType(pair.Value.Type) && !IsFloat(pair.Value.Type) && !ManagedTypes.IsNativePointer(pair.Value.Type)) return Fail<ManagedValue>(TypeFailure(pair.Value.Type), "使用了非整数形参位片");
            return Slice(pair.Value, low - start, width);
        }
        if (term.Kind == TermKind.Concat)
        {
            ManagedValue result = Constant(0, width); int offset = 0;
            foreach (var child in term.Operands)
            {
                if (low >= offset && low + width <= offset + child.Width)
                    return Part(child, low - offset, width, floating);
                int begin = Math.Max(low, offset), end = Math.Min(low + width, offset + child.Width);
                if (begin < end)
                {
                    var value = Part(child, begin - offset, end - begin); if (value is null) return null;
                    value = Convert(Mask(value, end - begin), width);
                    if (begin != low) value = Binary(BinaryOperator.ShiftLeft, value, Constant((ulong)(begin - low), 32), width);
                    result = Binary(BinaryOperator.Or, result, value, width);
                }
                offset += child.Width;
            }
            return Mask(result, width);
        }
        var whole = Value(term);
        return whole is null ? null : Slice(whole, low, width);
    }
    private ManagedValue Slice(ManagedValue value, int low, int width)
    {
        if (Opaque(value.Type))
        {
            if (low != 0 || width != value.Width) GenericFailure<object>("Arithmetic", "类型参数值不能拆分位片");
            return value;
        }
        if (ReferenceType(value.Type))
        {
            if (low != 0 || width != value.Width) Fail<object>(LoweringFailureKind.UnsupportedType, "引用的部分位片没有托管值表示");
            return value;
        }
        value = Convert(value, value.Width);
        if (low != 0) value = Binary(BinaryOperator.ShiftRightUnsigned, value, Constant((ulong)low, 32), value.Width);
        return Mask(value, width);
    }
    private ManagedValue? Operation(Term term, CoreOperation op, bool floating)
    {
        if (op == CoreOperation.Select && ConversionRefinement(term) is { } conversion)
            return Value(conversion);
        if (op.ToString().Contains("Float", StringComparison.Ordinal))
            return FloatOperation(term, op);
        var operands = term.Operands.Select((t, i) => Value(t, floating && op == CoreOperation.Select && i > 0)).ToArray();
        if (operands.Any(v => v is null)) return null;
        if (operands.Any(v => ReferenceType(v!.Type))
            && (op == CoreOperation.Select ? operands.Skip(1) : operands).Any(v => ManagedTypes.IsNativePointer(v!.Type)))
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "托管引用与原生整数或非托管指针共同参与运算", code: "lowering.NativeInt.Reference");
        if (operands.Any(v => Opaque(v!.Type)))
        {
            if (op == CoreOperation.Select && !Opaque(operands[0]!.Type))
            {
                var type = operands.Skip(1).First(v => Opaque(v!.Type))!.Type;
                return new ChoiceValue(operands[0]!, Coerce(operands[1]!, type), Coerce(operands[2]!, type), type, term.Width);
            }
            if (op is CoreOperation.Equal or CoreOperation.NotEqual && operands.Any(v => v is ConstantValue { Bits: 0 })
                && witness is not null && GenericWitness.IsCanonical(witness))
            {
                var parameter = operands.First(v => Opaque(v!.Type))!;
                return new ComparisonValue(op == CoreOperation.Equal ? ComparisonKind.Equal : ComparisonKind.NotEqual,
                    new BoxValue(parameter, parameter.Type, types.Object, types.PointerSize * 8),
                    new ConstantValue(0, types.Object, types.PointerSize * 8), types.Boolean);
            }
            return GenericFailure<ManagedValue>(op is CoreOperation.Equal or CoreOperation.NotEqual && operands.Any(v => v is ConstantValue { Bits: 0 })
                ? "NullTest" : "Arithmetic", "类型参数值参与尚未支持的运算：" + op);
        }
        if (operands.Any(v => ReferenceType(v!.Type)))
        {
            if (op is CoreOperation.Equal or CoreOperation.NotEqual)
            {
                var left = operands[0]!; var right = operands[1]!;
                if (left is ConstantValue { Bits: 0 }) left = Coerce(left, right.Type);
                if (right is ConstantValue { Bits: 0 }) right = Coerce(right, left.Type);
                if (!ReferenceType(left.Type) || !ReferenceType(right.Type))
                    return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "托管引用或地址用于与非零整数比较", code: "lowering.Address.Use");
                return new ComparisonValue(op == CoreOperation.Equal ? ComparisonKind.Equal : ComparisonKind.NotEqual, left, right, types.Boolean);
            }
            if (op == CoreOperation.Select)
            {
                var type = ReferenceType(operands[1]!.Type) ? operands[1]!.Type : operands[2]!.Type;
                return new ChoiceValue(operands[0]!, Coerce(operands[1]!, type), Coerce(operands[2]!, type), type, term.Width);
            }
            var address = op == CoreOperation.Add && locations is not null ? context.Get(locations.Addresses, term).Why : null;
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType, "引用参与非引用运算：" + op + (address is null ? "" : "；定位失败：" + address),
                address, address is null ? null : "lowering.Address.Location");
        }
        if (op == CoreOperation.Select && ManagedTypes.IsNativePointer(operands[1]!.Type)
            && Equals(operands[1]!.Type, operands[2]!.Type))
            return new ChoiceValue(IntegerBits(operands[0]!), operands[1]!, operands[2]!, operands[1]!.Type, term.Width);
        var a = IntegerBits(operands[0]!); var b = operands.Length > 1 ? IntegerBits(operands[1]!) : null;
        int width = term.Width, inputWidth = term.Operands[0].Width;
        switch (op)
        {
            case CoreOperation.Select when floating && width is 32 or 64:
                return new ChoiceValue(a, FloatBits(operands[1]!, width), FloatBits(operands[2]!, width), FloatType(width), width);
            case CoreOperation.Select: return new ChoiceValue(a, Convert(b!, width), Convert(operands[2]!, width), StackType(width), StackWidth(width));
            case CoreOperation.ZeroExtend: return Convert(Mask(a, inputWidth), width);
            case CoreOperation.SignExtend: return Mask(Convert(Signed(a, inputWidth), width, true), width);
            case CoreOperation.Truncate: return Mask(a, width);
            case CoreOperation.Negate: return Mask(new UnaryValue(UnaryOperator.Negate, a, StackType(width), StackWidth(width)), width);
            case CoreOperation.Not: return Mask(new UnaryValue(UnaryOperator.Not, a, StackType(width), StackWidth(width)), width);
            case CoreOperation.Equal: case CoreOperation.NotEqual:
            case CoreOperation.SignedLess: case CoreOperation.SignedLessEqual:
            case CoreOperation.UnsignedLess: case CoreOperation.UnsignedLessEqual:
                var signed = op is CoreOperation.SignedLess or CoreOperation.SignedLessEqual;
                var comparison = op switch
                {
                    CoreOperation.Equal => ComparisonKind.Equal, CoreOperation.NotEqual => ComparisonKind.NotEqual,
                    CoreOperation.SignedLess => ComparisonKind.SignedLess, CoreOperation.SignedLessEqual => ComparisonKind.SignedLessOrEqual,
                    CoreOperation.UnsignedLess => ComparisonKind.UnsignedLess, _ => ComparisonKind.UnsignedLessOrEqual,
                };
                return new ComparisonValue(comparison, signed ? Signed(a, inputWidth) : Mask(a, inputWidth),
                    signed ? Signed(b!, inputWidth) : Mask(b!, inputWidth), types.Boolean);
            case CoreOperation.ReverseBytes:
                ManagedValue reversed = Constant(0, width);
                for (int bit = 0; bit < width; bit += 8)
                {
                    var piece = Convert(Slice(a, bit, 8), width);
                    int target = width - bit - 8;
                    if (target != 0) piece = Binary(BinaryOperator.ShiftLeft, piece, Constant((ulong)target, 32), width);
                    reversed = Binary(BinaryOperator.Or, reversed, piece, width);
                }
                return Mask(reversed, width);
            case CoreOperation.RotateRight:
                var amount = Binary(BinaryOperator.And, Convert(b!, 32), Constant((ulong)(width - 1), 32), 32);
                if (width is not (32 or 64)) break;
                var opposite = new UnaryValue(UnaryOperator.Negate, amount, types.Int32, 32);
                return Binary(BinaryOperator.Or, Binary(BinaryOperator.ShiftRightUnsigned, a, amount, width),
                    Binary(BinaryOperator.ShiftLeft, a, opposite, width), width);
            case CoreOperation.SignedMultiplyHigh: case CoreOperation.UnsignedMultiplyHigh:
                if (width > 32) break;
                bool sign = op == CoreOperation.SignedMultiplyHigh;
                var product = Binary(BinaryOperator.Multiply, Convert(sign ? Signed(a, width) : a, 64, sign),
                    Convert(sign ? Signed(b!, width) : b!, 64, sign), 64);
                return Slice(product, width, width);
            default:
                BinaryOperator? binary = op switch
                {
                    CoreOperation.Add => BinaryOperator.Add, CoreOperation.Subtract => BinaryOperator.Subtract,
                    CoreOperation.Multiply => BinaryOperator.Multiply, CoreOperation.And => BinaryOperator.And,
                    CoreOperation.Or => BinaryOperator.Or, CoreOperation.Xor => BinaryOperator.Xor,
                    CoreOperation.SignedDivide => BinaryOperator.SignedDivide, CoreOperation.UnsignedDivide => BinaryOperator.UnsignedDivide,
                    CoreOperation.SignedRemainder => BinaryOperator.SignedRemainder, CoreOperation.UnsignedRemainder => BinaryOperator.UnsignedRemainder,
                    CoreOperation.ShiftLeft => BinaryOperator.ShiftLeft, CoreOperation.LogicalShiftRight => BinaryOperator.ShiftRightUnsigned,
                    CoreOperation.ArithmeticShiftRight => BinaryOperator.ShiftRightSigned, _ => null,
                };
                if (binary is null) break;
                if (op is CoreOperation.SignedDivide or CoreOperation.SignedRemainder or CoreOperation.ArithmeticShiftRight) a = Signed(a, inputWidth);
                if (op is CoreOperation.SignedDivide or CoreOperation.SignedRemainder) b = Signed(b!, inputWidth);
                if (op is CoreOperation.ShiftLeft or CoreOperation.LogicalShiftRight or CoreOperation.ArithmeticShiftRight) b = Convert(b!, 32);
                return Mask(Binary(binary.Value, a, b!, width), width);
        }
        return Fail<ManagedValue>(LoweringFailureKind.UnsupportedOperation, $"尚无等价的托管写法：{op}/{width}");
    }
}
