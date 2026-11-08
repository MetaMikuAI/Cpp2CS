using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Output;

/// <summary>单个方法的只读写出检查；不修改骨架、方法体或写出证据。</summary>
internal sealed class BodyValidation(ManagedTypes types, EmissionPolicy policy, MethodRef methodContext, DiagnosticOptions? diagnosticOptions = null)
{
    private readonly DiagnosticOptions diagnostics = diagnosticOptions ?? new();
    private TypeDef accessContext => methodContext.Method.Owner;
    private bool IgnoreAccess => policy != EmissionPolicy.Checked;
    private ulong? address;
    /// <summary>方法体从不写 this 也不取它的地址：ldarg.0 读到的始终是调用者传入的对象。</summary>
    private bool thisUnmodified;
    private bool CanAccess(MethodRef method, TypeRef? receiver) => IgnoreAccess || ManagedAccess.Method(types, accessContext, method, receiver);
    private bool CanAccess(TypeRef type) => IgnoreAccess || ManagedAccess.Type(types, accessContext, type);
    private bool CanAccess(FieldRef field, TypeRef? receiver) => IgnoreAccess || ManagedAccess.Field(types, methodContext, field, receiver);
    /// <summary>
    /// 构造函数之外写只读字段（member 表示写的是这个字段里面的成员）：放宽访问时 CIL 照写，源码工程放宽主程序集自己的声明（SourceReferences）；
    /// 别的程序集的只读字段整个写入时，源码层把覆盖全部字段的连续写入换回构造函数，写它里面的成员则写不出来（CS1648）。
    /// </summary>
    private bool WritesReadonly(FieldRef field, bool member) => !IgnoreAccess || member && field.Field.Owner.Assembly != methodContext.Method.Owner.Assembly;

    public EmissionProblem? Check(ManagedBody recovered, bool hasBody)
    {
        var problem = Validate(recovered, hasBody);
        return problem is null ? null : problem with { Method = methodContext, Address = address };
    }

    private EmissionProblem? Validate(ManagedBody recovered, bool hasBody)
    {
        if (!hasBody) return new(EmissionProblemKind.Unsupported, "方法不允许 CIL 方法体");
        if (recovered.Blocks.Count == 0) return new(EmissionProblemKind.Unsupported, "空控制流图");
        var blockAddresses = recovered.Blocks.Select(b => b.Address).ToHashSet();
        if (blockAddresses.Count != recovered.Blocks.Count) return new(EmissionProblemKind.Unsupported, "控制流 块地址重复，无法唯一确定跳转标签");
        foreach (var edge in recovered.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges))
            if (!blockAddresses.Contains(edge.Target)) return new(EmissionProblemKind.Unsupported, $"控制流 跳转目标 0x{edge.Target:x} 不在方法体中");
        if (methodContext.Method.Name == ".ctor" && !methodContext.Method.IsStatic && !methodContext.Method.Owner.IsValueType)
        {
            if (ConstructorInitialization.Check(recovered, out _) is { } initializationProblem) return new(EmissionProblemKind.Constructor, initializationProblem);
        }
        thisUnmodified = !methodContext.Method.IsStatic && !recovered.Blocks.SelectMany(b => b.Statements).Any(statement =>
            statement is ManagedStore { Target: ArgumentValue { Index: -1 } }
            || ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk)
                .Any(v => v is AddressValue { Target: ArgumentValue { Index: -1 } }));
        foreach (var statement in recovered.Blocks.SelectMany(b => b.Statements))
        {
            address = statement.Address;
            if (statement is ManagedAssignment assignment && ScalarCopyProblem(assignment.Target, assignment.Value) is { } assignmentProblem)
                return assignmentProblem;
            foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies))
                if (ScalarCopyProblem(copy.Target, copy.Value) is { } copyProblem) return copyProblem;
            if (statement is ManagedCall { Invocation.Constraint: { } constraint } constrained
                && (!constrained.Invocation.Virtual || constrained.Invocation.Method.Method.IsStatic
                    || constrained.Invocation.Receiver?.Type is not ByRefRef reference || !reference.Element.Equals(constraint)))
                return new(EmissionProblemKind.Unsupported, "受约束调用需要同类型托管地址与实例 callvirt");
            if (statement is ManagedCall c && !CanAccess(c.Invocation.Method, c.Invocation.Receiver?.Type))
                return new(EmissionProblemKind.AccessDenied, $"访问权限 调用 {c.Invocation.Method}");
            if (statement is ManagedCall { Inlined: true } inlined
                && !ManagedAccess.Method(types, accessContext, inlined.Invocation.Method, inlined.Invocation.Receiver?.Type))
                return new(EmissionProblemKind.AccessDenied, $"访问权限 内联证明调用 {inlined.Invocation.Method}");
            if (statement is ManagedStore store && (StaticWriteProblem(store.Target) ?? ReadonlyWriteProblem(store.Target)) is { } writeProblem)
            {
                if (diagnostics.Emit) diagnostics.Write("emit", statement.Address, $"  [写出问题] 0x{statement.Address:x} {statement}");
                return writeProblem;
            }
            if (statement is ManagedStore { Target: not (FieldValue or StaticFieldValue or ArrayElementValue or IndirectValue) }) return new(EmissionProblemKind.Unsupported, "写入位置不是字段或数组元素");
            if (statement is ManagedCheck check && !CanAccess(check.Exception, null)) return new(EmissionProblemKind.AccessDenied, $"访问权限 异常构造 {check.Exception}");
            var values = ManagedValues.Of(statement).Concat(statement switch
            {
                ManagedJump or ManagedBranch or ManagedSwitch => ManagedValues.Edges(statement).SelectMany(e => e.Copies).SelectMany(c => new ManagedValue[] { c.Target, c.Value }),
                _ => [],
            });
            foreach (var value in values)
            {
                foreach (var nested in ManagedValues.Walk(value))
                    if (AccessorProblem(nested, statement is ManagedStore s && ReferenceEquals(nested, s.Target)) is { } accessFailure) return accessFailure;
                if (Problem(value) is { } problem)
                {
                    if (diagnostics.Emit) diagnostics.Write("emit", statement.Address, $"  [写出问题] 0x{statement.Address:x} {statement}");
                    return problem;
                }
            }
        }
        return null;
    }

    private EmissionProblem? ScalarCopyProblem(LocalValue target, ManagedValue value)
    {
        var to = types.Kind(target.Type);
        var from = types.Kind(value.Type);
        return to is TypeKind.Int or TypeKind.Bool && from is TypeKind.Float or TypeKind.Double
            || from is TypeKind.Int or TypeKind.Bool && to is TypeKind.Float or TypeKind.Double
            ? new(EmissionProblemKind.Unsupported, "局部赋值 整数与浮点之间缺少显式转换") : null;
    }

    private EmissionProblem? Problem(ManagedValue value)
    {
        // async void 的完成标记不产生栈值，不能按普通值要求非零位宽。
        if (value is AsyncResultValue { Value: null } && ManagedTypes.IsVoid(value.Type)) return null;
        // 开放 T 的大小由 CLR 决定；仅保留有类型的复制、字段、局部和 default(T)。
        var genericStorage = value.Type is GenericParameterRef && value is ArgumentValue or LocalValue or FieldValue or IndirectValue or UnboxValue or ComposedValue { Leaves.Count: 0 };
        if (value.Width is not (1 or 8 or 16 or 32 or 64) && !(value.Width == 0 && (types.Kind(value.Type) == TypeKind.Struct || genericStorage))) return new(EmissionProblemKind.Unsupported, $"位宽 {value.Width} 尚未支持");
        // C# 里每个值的类型都可能要按名写出（局部变量声明、转换）
        if (!CanAccess(value.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 类型 {value.Type}");
        foreach (var operand in FloatingOperands(value))
            if (operand.Width is not (32 or 64) || types.Bits(operand.Type) != operand.Width
                || types.Kind(operand.Type) is not (TypeKind.Float or TypeKind.Double)
                    && BitConversions.Find(types, operand.Type, operand.Width == 32 ? types.Single : types.Double) is null)
                return new(EmissionProblemKind.Unsupported, $"浮点操作 类型 {operand.Type}/{operand.Width} 缺少同宽标量表示");
        switch (value)
        {
            case ArgumentValue argument when argument.Index < -1 || argument.Index == -1 && methodContext.Method.IsStatic
                || argument.Index >= methodContext.Method.Parameters.Count:
                return new(EmissionProblemKind.Unsupported, $"参数 索引 {argument.Index} 不在方法签名中");
            case DelegateValue delegated:
                if (DelegateProblem(delegated) is { } delegateProblem) return delegateProblem;
                break;
            case StringValue: return value.Type.Equals(types.String) ? null : new(EmissionProblemKind.Unsupported, "字符串常量类型不符");
            case HoleValue: return null;
            case AsyncResultValue: break;
            case TypeHandleValue handle:
                if (!CanAccess(handle.Target)) return new(EmissionProblemKind.AccessDenied, $"访问权限 类型 {handle.Target}");
                return handle.Type.Equals(types.RuntimeTypeHandle) ? null : new(EmissionProblemKind.Unsupported, "类型句柄的托管类型不符");
            case FieldHandleValue handle:
                return handle.Type.Equals(types.RuntimeFieldHandle) ? null : new(EmissionProblemKind.Unsupported, "字段句柄的托管类型不符");
            case StaticCallValue call:
                return call.Method.Method is { IsStatic: true, Parameters.Count: 0 } && CanAccess(call.Method, null) ? null : new(EmissionProblemKind.Unsupported, $"静态调用 {call.Method}");
            case MethodHandleValue handle:
                return handle.Type.Equals(types.RuntimeMethodHandle) ? null : new(EmissionProblemKind.Unsupported, "方法句柄的托管类型不符");
            case NewObjectValue created:
                var constructor = created.Constructor;
                if (constructor.Method.Name != ".ctor" || constructor.Method.IsStatic || constructor.Method.Parameters.Count != created.Arguments.Count)
                    return new(EmissionProblemKind.Unsupported, "构造 不是实例构造函数或参数个数不符");
                if (!CanAccess(constructor, created.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 构造 {constructor}");
                break;
            case NewArrayValue array:
                if (!array.ArrayType.IsVector) return new(EmissionProblemKind.Unsupported, "数组 分配需要一维向量类型");
                break;
            case BoxValue box:
                if (!CanAccess(box.Boxed)) return new(EmissionProblemKind.AccessDenied, $"访问权限 类型 {box.Boxed}");
                if (box.Boxed is not GenericParameterRef && !Boxable(box.Boxed)) return new(EmissionProblemKind.Unsupported, $"装箱 类型 {box.Boxed}");
                break;
            case UnboxAddressValue unbox:
                if (!CanAccess(unbox.Target)) return new(EmissionProblemKind.AccessDenied, $"访问权限 类型 {unbox.Target}");
                if (!Boxable(unbox.Target)
                    && unbox.Target is not GenericParameterRef { NativeScalar: not null }) return new(EmissionProblemKind.Unsupported, $"拆箱 类型 {unbox.Target} 尚未支持");
                break;
            case UnboxValue unbox:
                if (!ManagedTypes.IsReferenceType(unbox.Operand.Type)) return new(EmissionProblemKind.Unsupported, "拆箱值需要对象来源");
                break;
            case CheckedCastValue cast:
                if (!ManagedTypes.IsReferenceType(cast.Operand.Type) || !ManagedTypes.IsReferenceType(cast.Target))
                    return new(EmissionProblemKind.Unsupported, "引用转换 需要引用类型的来源与目标");
                break;
            case ArrayLengthValue length:
                if (length.Array.Type is not ArrayRef { IsVector: true }) return new(EmissionProblemKind.Unsupported, "数组 长度需要一维向量类型");
                break;
            case StringLengthValue length:
                if (!length.String.Type.Equals(types.String) || !length.Type.Equals(types.Int32)) return new(EmissionProblemKind.Unsupported, "字符串 长度类型不符");
                break;
            case ArrayElementValue element:
                if (element.Array.Type is not ArrayRef { IsVector: true } a || !element.Type.Equals(a.Element)) return new(EmissionProblemKind.Unsupported, "数组 元素类型不符");
                break;
            case PinnedArrayValue pinned:
                if (!pinned.Array.Type.Equals(pinned.ArrayType) || !pinned.ArrayType.IsVector
                    || !types.Unmanaged(pinned.ArrayType.Element)) return new(EmissionProblemKind.Unsupported, "固定地址 需要非托管元素的一维数组");
                break;
            case PointerOffsetValue pointer:
                if (pointer.Pointer.Type is not PointerRef || pointer.Offset.Width != 64 || types.Kind(pointer.Offset.Type) != TypeKind.Int) return new(EmissionProblemKind.Unsupported, "指针偏移 类型或位宽不符");
                break;
            case ConstantValue c:
                if (!(types.Kind(c.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double
                    || c.Bits == 0 && (ManagedTypes.IsReferenceType(c.Type) || ManagedTypes.IsNativePointer(c.Type) || c.Type is ByRefRef)))
                    return new(EmissionProblemKind.Unsupported, $"常量 类型 {c.Type}");
                break;
            case ComposedValue c:
                foreach (var leaf in c.Leaves)
                    foreach (var field in leaf.Path)
                    {
                        if (!c.Unfolded && !CanAccess(field, field.DeclaringType)) return new(EmissionProblemKind.AccessDenied, $"访问权限 字段 {field}");
                        if (!IgnoreAccess && (field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
                            && !(methodContext.Method.Name == ".ctor" && methodContext.Method.Owner == field.Field.Owner))
                            return new(EmissionProblemKind.ReadonlyInstanceField, $"只读实例字段 不能逐叶子合成 {field.DeclaringType}：{field}");
                    }
                break;
            case AddressValue takenAddress:
                if (!Addressable(takenAddress.Target)) return new(EmissionProblemKind.Unsupported, "取址 需要托管存储位置");
                // 放宽访问时取只读字段的地址照写：只读的调用接收者在 C# 里由编译器做防御性复制，真正的写入在写入语句处检查。
                if (!IgnoreAccess && ReadonlyWriteProblem(takenAddress.Target) is { } readonlyProblem) return readonlyProblem;
                break;
            case FieldValue f:
                if (f.Accessor is { } instanceAccessor ? !instanceAccessor.Matches(types, accessContext, f, instanceAccessor.Write) : !f.Unfolded && !CanAccess(f.Field, f.Receiver.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 字段 {f.Field}");
                return Problem(f.Receiver is AddressValue address ? address.Target : f.Receiver);
            case StaticFieldValue f:
                if (!f.Field.Field.IsStatic || (f.Field.Field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                    return new(EmissionProblemKind.Unsupported, "静态字段 存储类型不符");
                if (f.Accessor is { } staticAccessor ? !staticAccessor.Matches(types, accessContext, f, staticAccessor.Write) : !f.Unfolded && !CanAccess(f.Field, null)) return new(EmissionProblemKind.AccessDenied, $"访问权限 静态字段 {f.Field}");
                break;
            case ConversionValue { Kind: ConvKind.Bitcast } bitcast
                when (types.Kind(bitcast.Operand.Type) is TypeKind.Float or TypeKind.Double) != (types.Kind(bitcast.Type) is TypeKind.Float or TypeKind.Double):
                if (bitcast.Width != bitcast.Operand.Width || bitcast.Width != types.Bits(bitcast.Type)
                    || BitConversions.Find(types, bitcast.Operand.Type, bitcast.Type) is null)
                    return new(EmissionProblemKind.Unsupported, "转换 浮点位重解释缺少同宽核心库方法");
                break;
            case BinaryValue b:
                if (b.Width == 0 || b.Left.Width == 0 || b.Right.Width == 0)
                    return new(EmissionProblemKind.Unsupported, "运算 缺少标量位宽");
                if (CilOperators.Binary(b.Op) is null && !CilOperators.NativeArithmetic(b.Op))
                    return new(EmissionProblemKind.Unsupported, $"运算 {b.Op} 尚未支持 CIL 写出");
                if (CilOperators.NativeArithmetic(b.Op) && b.Width is not (32 or 64))
                    return new(EmissionProblemKind.Unsupported, $"运算 {b.Op} 需要 32 或 64 位标量");
                // CIL rem 对零除数和 MinValue rem -1 抛出，ARM64 没有对应的取余指令，只写出不会抛出的常量除数。
                if (b.Op is BinOp.SRem or BinOp.URem && (b.Right is not ConstantValue { Bits: var divisor }
                    || (divisor & Expr.Mask(b.Width)) == 0 || b.Op == BinOp.SRem && (divisor & Expr.Mask(b.Width)) == Expr.Mask(b.Width)))
                    return new(EmissionProblemKind.Unsupported, $"运算 {b.Op} 需要不会抛出的常量除数");
                if (b.Left.Width != b.Width || b.Right.Width != b.Width && b.Op is not (BinOp.Shl or BinOp.LShr or BinOp.AShr)) return new(EmissionProblemKind.Unsupported, "运算 位宽不一致");
                break;
            case UnaryValue u:
                if (u.Width == 0 || u.Operand.Width == 0)
                    return new(EmissionProblemKind.Unsupported, "运算 缺少标量位宽");
                if (CilOperators.Unary(u.Op) is null && CilOperators.Math(u.Op) is null)
                    return new(EmissionProblemKind.Unsupported, $"运算 {u.Op} 尚未支持 CIL 写出");
                break;
            case ConversionValue { Kind: ConvKind.FloatToSInt or ConvKind.FloatToUInt, Width: not (32 or 64) }:
                return new(EmissionProblemKind.Unsupported, "浮点转换 目标需要 32 或 64 位整数");
            case ConversionValue c when c.Type is not GenericParameterRef { NativeScalar: not null }
                && c.Kind != ConvKind.Bitcast && (c.Width == 0 || c.Operand.Width == 0):
                return new(EmissionProblemKind.Unsupported, "转换 缺少标量位宽");
            case ComparisonValue c:
                if ((c.Left.Width == 0 || c.Right.Width == 0)
                    && !ManagedTypes.IsReferenceType(c.Left.Type) && !ManagedTypes.IsReferenceType(c.Right.Type))
                    return new(EmissionProblemKind.Unsupported, "比较 非引用操作数缺少标量位宽");
                if (c.Condition is not (Cond.Eq or Cond.Ne or Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge or Cond.Ult or Cond.Ule or Cond.Ugt or Cond.Uge
                    or Cond.FEq or Cond.FNe or Cond.FUne or Cond.FLt or Cond.FLe or Cond.FGt or Cond.FGe or Cond.FUlt or Cond.FUle or Cond.FUgt or Cond.FUge
                    or Cond.FOrdered or Cond.FUnordered))
                    return new(EmissionProblemKind.Unsupported, $"比较 {c.Condition} 尚未支持");
                break;
        }
        foreach (var child in ManagedValues.Children(value))
            if (Problem(child) is { } problem) return problem;
        return null;
    }

    private IEnumerable<ManagedValue> FloatingOperands(ManagedValue value) => value switch
    {
        ConversionValue { Type: GenericParameterRef { NativeScalar: not null } } => [],
        ConversionValue { Kind: ConvKind.FloatToFloat or ConvKind.FloatToSInt or ConvKind.FloatToUInt } c => [c.Operand],
        UnaryValue { Op: UnOp.FNeg or UnOp.FAbs or UnOp.FSqrt or UnOp.FFloor or UnOp.FCeil or UnOp.FTrunc or UnOp.FRoundEven } u => [u.Operand],
        BinaryValue b when b.Op is BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber
            || b.Op is not (BinOp.SDiv or BinOp.UDiv) && types.Kind(b.Type) is TypeKind.Float or TypeKind.Double => [b.Left, b.Right],
        ComparisonValue { Condition: Cond.FEq or Cond.FNe or Cond.FUne or Cond.FLt or Cond.FLe or Cond.FGt or Cond.FGe
            or Cond.FUlt or Cond.FUle or Cond.FUgt or Cond.FUge or Cond.FOrdered or Cond.FUnordered } c => [c.Left, c.Right],
        _ => [],
    };

    private bool Addressable(ManagedValue value) => value switch
    {
        ArgumentValue { Index: >= 0 } or LocalValue or IndirectValue or StaticFieldValue or ArrayElementValue => true,
        FieldValue field => types.Kind(field.Receiver.Type) != TypeKind.Struct || Addressable(field.Receiver),
        _ => false,
    };

    private EmissionProblem? StaticWriteProblem(ManagedValue target) =>
        !IgnoreAccess && target is StaticFieldValue storage && (storage.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(methodContext.Method is { Name: ".cctor", IsStatic: true } && methodContext.Method.Owner == storage.Field.Field.Owner)
            ? new(EmissionProblemKind.ReadonlyStaticField, $"只读静态字段 只能在本类静态构造函数中写入: {storage.Field.Field}") : null;

    private EmissionProblem? AccessorProblem(ManagedValue value, bool write)
    {
        var accessor = value switch { FieldValue f => f.Accessor, StaticFieldValue f => f.Accessor, _ => null };
        if (accessor is null) return null;
        return accessor.Matches(types, accessContext, value, write) ? null : new(EmissionProblemKind.AccessDenied, "访问权限 访问器证明与字段访问不符");
    }

    // IntPtr/UIntPtr 是可装箱的 CLR 值类型；裸指针与托管地址仍不可装箱。
    private bool Boxable(TypeRef type) => types.Kind(type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Struct
        || type.Equals(types.IntPtr) || type.Equals(types.Corlib("System.UIntPtr"));

    private EmissionProblem? DelegateProblem(DelegateValue value)
    {
        if (DelegateFacts.Constructor(value.DelegateType) is not { } constructor) return new(EmissionProblemKind.Unsupported, "委托 缺少标准构造");
        if (!CanAccess(constructor, value.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 委托构造 {constructor}");
        if (!CanAccess(value.Method, value.Binding == DelegateBinding.Static ? null : value.Target.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 委托方法 {value.Method}");
        // 直接 Method 符号不能换成 ldvirtftn。非 final 的虚方法用 ldftn 绑定时，CLI 验证要求接收者类型封闭，
        // 或接收者是未被修改的 this（引用类型中 ldarg.0 后 ldftn 基类方法，即 C# 的 base.M 委托）。
        if (value.Binding != DelegateBinding.VirtualInstance && value.Method.Method.IsVirtual && (value.Method.Method.Attributes & System.Reflection.MethodAttributes.Final) == 0
            && value.Target.Type is Cpp2CS.Model.DefinitionRef d && (d.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) == 0
            && !(value.Target is ArgumentValue { Index: -1 } && thisUnmodified && !methodContext.Method.Owner.IsValueType))
            return new(EmissionProblemKind.Unsupported, "委托 直接虚方法绑定的验证条件未证明");
        return null;
    }

    private EmissionProblem? ReadonlyWriteProblem(ManagedValue value, bool member = false)
    {
        if (value is AddressValue a) return ReadonlyWriteProblem(a.Target, member);
        if (value is IndirectValue indirect) return ReadonlyWriteProblem(indirect.Address, member);
        if (value is not FieldValue field) return null;
        if (WritesReadonly(field.Field, member) && (field.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(methodContext.Method.Name == ".ctor" && methodContext.Method.Owner == field.Field.Field.Owner))
            return new(EmissionProblemKind.ReadonlyInstanceField, $"只读实例字段 不能在所属类型构造函数之外取得可写地址：{field.Field}");
        if (field.Receiver is AddressValue address) return ReadonlyWriteProblem(address.Target, true);
        return null;
    }

}
