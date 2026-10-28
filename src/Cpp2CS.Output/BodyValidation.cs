using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>单个方法的只读写出检查；不修改骨架、方法体或写出证据。</summary>
internal sealed class BodyValidation(ManagedTypes types, EmissionPolicy policy, MethodRef methodContext)
{
    private TypeDef accessContext => methodContext.Method.Owner;
    private bool IgnoreAccess => policy != EmissionPolicy.Checked;
    private ulong? address;
    private bool CanAccess(MethodRef method, TypeRef? receiver) => IgnoreAccess || ManagedAccess.Method(types, accessContext, method, receiver);
    private bool CanAccess(TypeRef type) => IgnoreAccess || ManagedAccess.Type(types, accessContext, type);
    private bool CanAccess(FieldRef field, TypeRef? receiver) => IgnoreAccess || ManagedAccess.Field(types, accessContext, field, receiver);

    public EmissionProblem? Check(ManagedBody recovered, bool hasBody, out ConstructorInitialization.Shape? shape)
    {
        var problem = Validate(recovered, hasBody, out shape);
        return problem is null ? null : problem with { Method = methodContext, Address = address };
    }

    private EmissionProblem? Validate(ManagedBody recovered, bool hasBody, out ConstructorInitialization.Shape? shape)
    {
        shape = null;
        if (!hasBody) return new(EmissionProblemKind.Unsupported, "方法不允许 CIL 方法体");
        if (recovered.Blocks.Count == 0) return new(EmissionProblemKind.Unsupported, "空控制流图");
        var blockAddresses = recovered.Blocks.Select(b => b.Address).ToHashSet();
        if (blockAddresses.Count != recovered.Blocks.Count) return new(EmissionProblemKind.Unsupported, "控制流 块地址重复，无法唯一确定跳转标签");
        foreach (var edge in recovered.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges))
            if (!blockAddresses.Contains(edge.Target)) return new(EmissionProblemKind.Unsupported, $"控制流 跳转目标 0x{edge.Target:x} 不在方法体中");
        if (methodContext.Method.Name == ".ctor" && !methodContext.Method.IsStatic && !methodContext.Method.Owner.IsValueType)
        {
            if (ConstructorInitialization.Check(recovered, out var constructorShape) is { } initializationProblem) return new(EmissionProblemKind.Constructor, initializationProblem);
            shape = constructorShape;
        }
        foreach (var statement in recovered.Blocks.SelectMany(b => b.Statements))
        {
            address = statement.Address;
            if (statement is ManagedCall { Invocation.Constraint: { } constraint } constrained
                && (!constrained.Invocation.Virtual || constrained.Invocation.Method.Method.IsStatic
                    || constrained.Invocation.Receiver?.Type is not ByRefRef reference || !reference.Element.Equals(constraint)))
                return new(EmissionProblemKind.Unsupported, "受约束调用需要同类型托管地址与实例 callvirt");
            if (statement is ManagedCall c && !CanAccess(c.Invocation.Method, c.Invocation.Receiver?.Type))
                return new(EmissionProblemKind.AccessDenied, $"访问权限 调用 {c.Invocation.Method}");
            if (statement is ManagedStore store && (StaticWriteProblem(store.Target) ?? ReadonlyWriteProblem(store.Target)) is { } writeProblem)
            {
                if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1") Console.Error.WriteLine($"  [写出问题] 0x{statement.Address:x} {statement}");
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
                    if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1") Console.Error.WriteLine($"  [写出问题] 0x{statement.Address:x} {statement}");
                    return problem;
                }
            }
        }
        return null;
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
        switch (value)
        {
            case DelegateValue delegated:
                if (DelegateProblem(delegated) is { } delegateProblem) return delegateProblem;
                break;
            case StringValue: return value.Type.Equals(types.String) ? null : new(EmissionProblemKind.Unsupported, "字符串常量类型不符");
            case HoleValue: return null;
            case AsyncResultValue: break;
            case TypeHandleValue handle:
                if (!CanAccess(handle.Target)) return new(EmissionProblemKind.AccessDenied, $"访问权限 类型 {handle.Target}");
                return handle.Type.Equals(types.RuntimeTypeHandle) ? null : new(EmissionProblemKind.Unsupported, "类型句柄的托管类型不符");
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
                if (box.Boxed is not GenericParameterRef && types.Kind(box.Boxed) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Struct)) return new(EmissionProblemKind.Unsupported, $"装箱 类型 {box.Boxed}");
                if (box.Boxed is DefinitionRef { Definition.FullName: "System.Nullable" }) return new(EmissionProblemKind.Unsupported, "装箱 Nullable 尚未支持");
                break;
            case UnboxAddressValue unbox:
                if (!CanAccess(unbox.Target)) return new(EmissionProblemKind.AccessDenied, $"访问权限 类型 {unbox.Target}");
                if (unbox.Target is not (DefinitionRef { Definition.IsEnum: true } or GenericParameterRef { NativeScalar: not null })) return new(EmissionProblemKind.Unsupported, $"拆箱 类型 {unbox.Target} 尚未支持");
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
            case ArrayElementValue element:
                if (element.Array.Type is not ArrayRef { IsVector: true } a || !element.Type.Equals(a.Element)) return new(EmissionProblemKind.Unsupported, "数组 元素类型不符");
                break;
            case PinnedArrayValue pinned:
                if (!pinned.Array.Type.Equals(pinned.ArrayType) || !pinned.ArrayType.IsVector
                    || types.Kind(pinned.ArrayType.Element) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double)) return new(EmissionProblemKind.Unsupported, "固定地址 需要基元一维数组");
                break;
            case PointerOffsetValue pointer:
                if (pointer.Pointer.Type is not PointerRef || pointer.Offset.Width != 64 || types.Kind(pointer.Offset.Type) != TypeKind.Int) return new(EmissionProblemKind.Unsupported, "指针偏移 类型或位宽不符");
                break;
            case ConstantValue c:
                if (!(types.Kind(c.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double
                    || c.Bits == 0 && (ManagedTypes.IsReferenceType(c.Type) || ManagedTypes.IsNativePointer(c.Type))))
                    return new(EmissionProblemKind.Unsupported, $"常量 类型 {c.Type}");
                break;
            case ComposedValue c:
                foreach (var leaf in c.Leaves)
                    foreach (var field in leaf.Path)
                    {
                        if (!CanAccess(field, field.DeclaringType)) return new(EmissionProblemKind.AccessDenied, $"访问权限 字段 {field}");
                        if (!IgnoreAccess && (field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
                            && !(methodContext.Method.Name == ".ctor" && methodContext.Method.Owner == field.Field.Owner))
                            return new(EmissionProblemKind.ReadonlyInstanceField, $"只读实例字段 不能逐叶子合成 {field.DeclaringType}：{field}");
                    }
                break;
            case AddressValue takenAddress:
                if (ReadonlyWriteProblem(takenAddress.Target) is { } readonlyProblem) return readonlyProblem;
                break;
            case FieldValue f:
                if (f.Accessor is { } instanceAccessor ? !instanceAccessor.Matches(types, accessContext, f, instanceAccessor.Write) : !CanAccess(f.Field, f.Receiver.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 字段 {f.Field}");
                return Problem(f.Receiver is AddressValue address ? address.Target : f.Receiver);
            case StaticFieldValue f:
                if (!f.Field.Field.IsStatic || (f.Field.Field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                    return new(EmissionProblemKind.Unsupported, "静态字段 存储类型不符");
                if (f.Accessor is { } staticAccessor ? !staticAccessor.Matches(types, accessContext, f, staticAccessor.Write) : !CanAccess(f.Field, null)) return new(EmissionProblemKind.AccessDenied, $"访问权限 静态字段 {f.Field}");
                break;
            case ConversionValue { Kind: ConvKind.Bitcast } bitcast
                when (types.Kind(bitcast.Operand.Type) is TypeKind.Float or TypeKind.Double) != (types.Kind(bitcast.Type) is TypeKind.Float or TypeKind.Double):
                if (bitcast.Width != bitcast.Operand.Width || bitcast.Width != types.Bits(bitcast.Type)
                    || BitConversions.Find(types, bitcast.Operand.Type, bitcast.Type) is null)
                    return new(EmissionProblemKind.Unsupported, "转换 浮点位重解释缺少同宽核心库方法");
                break;
            case BinaryValue b:
                if (b.Left.Width != b.Width || b.Right.Width != b.Width && b.Op is not (BinOp.Shl or BinOp.LShr or BinOp.AShr)) return new(EmissionProblemKind.Unsupported, "运算 位宽不一致");
                break;
            case ComparisonValue c:
                if (c.Condition is not (Cond.Eq or Cond.Ne or Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge or Cond.Ult or Cond.Ule or Cond.Ugt or Cond.Uge
                    or Cond.FEq or Cond.FUne or Cond.FLt or Cond.FLe or Cond.FGt or Cond.FGe or Cond.FUlt or Cond.FUle or Cond.FUgt or Cond.FUge))
                    return new(EmissionProblemKind.Unsupported, $"比较 {c.Condition} 尚未支持");
                break;
        }
        foreach (var child in ManagedValues.Children(value))
            if (Problem(child) is { } problem) return problem;
        return null;
    }

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

    private EmissionProblem? DelegateProblem(DelegateValue value)
    {
        if (DelegateFacts.Constructor(value.DelegateType) is not { } constructor) return new(EmissionProblemKind.Unsupported, "委托 缺少标准构造");
        if (!CanAccess(constructor, value.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 委托构造 {constructor}");
        if (!CanAccess(value.Method, value.Binding == DelegateBinding.Static ? null : value.Target.Type)) return new(EmissionProblemKind.AccessDenied, $"访问权限 委托方法 {value.Method}");
        // 直接 Method 符号不能换成 ldvirtftn。非 final 的虚方法只有接收者类型封闭时才采用此序列。
        if (value.Binding != DelegateBinding.VirtualInstance && value.Method.Method.IsVirtual && (value.Method.Method.Attributes & System.Reflection.MethodAttributes.Final) == 0
            && value.Target.Type is Cpp2CS.Model.DefinitionRef d && (d.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) == 0)
            return new(EmissionProblemKind.Unsupported, "委托 直接虚方法绑定的验证条件未证明");
        return null;
    }

    private EmissionProblem? ReadonlyWriteProblem(ManagedValue value)
    {
        if (value is AddressValue a) return ReadonlyWriteProblem(a.Target);
        if (value is IndirectValue indirect) return ReadonlyWriteProblem(indirect.Address);
        if (value is not FieldValue field || IgnoreAccess) return null;
        if ((field.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(methodContext.Method.Name == ".ctor" && methodContext.Method.Owner == field.Field.Field.Owner))
            return new(EmissionProblemKind.ReadonlyInstanceField, $"只读实例字段 不能在所属类型构造函数之外取得可写地址：{field.Field}");
        if (field.Receiver is AddressValue address) return ReadonlyWriteProblem(address.Target);
        return null;
    }

}
