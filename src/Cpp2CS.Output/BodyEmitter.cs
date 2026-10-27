using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>
/// 把 L3 的托管方法体写成 CIL：每个 SSA 局部变量一个 IL 局部变量，边赋值先读后写，
/// 整数运算后按值的位宽与符号规范化。先检查支持范围（访问权限、构造函数的 this 初始化、各类值），不支持时不替换骨架方法体。
/// 通过原有检查后统一应用 ReadabilityRewriter；recover 与执行对照共享此入口。
/// </summary>
public sealed partial class BodyEmitter
{
    private readonly ManagedTypes types;
    private readonly Skeleton skeleton;
    private readonly Dictionary<Variable, VariableDefinition> locals = new();
    private readonly Dictionary<ulong, Instruction> labels = new();
    private readonly Dictionary<ModuleDefinition, (MethodReference At, MethodReference Fail, MethodDefinition Value)> unrecovered = new();
    private readonly Dictionary<ModuleDefinition, (MethodDefinition Of, MethodDefinition Do, MethodDefinition Result, MethodDefinition Completed, MethodDefinition CompletedVoid)> awaits = new();
    private MethodDefinition destination = null!;
    private MethodBody body = null!;
    private ILProcessor il = null!;
    private TypeDef accessContext = null!;
    private MethodRef methodContext = null!;
    // 显式原生整区清零对应的指令，供变异检查定位；Compose 的临时值初始化不在此集合。
    public HashSet<Instruction> ExplicitInitializations { get; } = [];

    /// <summary>
    /// 放行越权访问：内联进来的代码对别的类型私有成员（含只读字段）的直接访问按原样写出，语义等价，但对着原程序集编译不过。
    /// 只在认回访问器之后的最终写出打开（<see cref="AccessorRecovery.Rewrite"/>），访问器候选仍从越权失败中发现。
    /// </summary>
    public bool IgnoreAccess { get; set; }

    private bool CanAccess(MethodRef method, TypeRef? receiver) => IgnoreAccess || ManagedAccess.Method(types, accessContext, method, receiver);
    private bool CanAccess(TypeRef type) => IgnoreAccess || ManagedAccess.Type(types, accessContext, type);
    private bool CanAccess(FieldRef field, TypeRef? receiver) => IgnoreAccess || ManagedAccess.Field(types, accessContext, field, receiver);

    public BodyEmitter(Skeleton skeleton, ManagedTypes types)
    {
        this.skeleton = skeleton;
        this.types = types;
    }

    private TypeReference TypeReference(TypeRef type) => skeleton.Reference(destination.Module, type, destination.DeclaringType, destination);
    private FieldReference FieldReference(FieldRef field) => skeleton.Reference(destination.Module, field, destination.DeclaringType, destination);
    private MethodReference MethodReference(MethodRef method) => skeleton.Reference(destination.Module, method, destination.DeclaringType, destination);

    /// <summary>
    /// 写出一组方法体，返回不能写出的方法体及原因，这些方法保持骨架方法体。
    /// 同一类型的构造函数要一起判定：字段初始化器必须在本类所有构造函数中一致（见 <see cref="ConstructorInitialization"/>）。
    /// </summary>
    public Dictionary<ManagedBody, string> Emit(IEnumerable<ManagedBody> bodies)
    {
        var readability = ReadabilityRewriter.FromEnvironment();
        var problems = new Dictionary<ManagedBody, string>(ReferenceEqualityComparer.Instance);
        var accepted = new List<(ManagedBody Body, MethodDefinition Method)>();
        var constructors = new List<(ManagedBody, ConstructorInitialization.Shape)>();
        foreach (var recovered in bodies)
        {
            var method = skeleton.Method(recovered.Method.Method);
            if (Validate(recovered, method, out var shape) is { } problem) problems.Add(recovered, problem);
            else
            {
                accepted.Add((recovered, method));
                if (shape is not null) constructors.Add((recovered, shape));
            }
        }
        foreach (var constructor in ConstructorInitialization.Inconsistent(constructors))
            problems.Add(constructor, "构造函数 有字段初始化器，要求本类所有构造函数都已写出且初始化器相同");
        foreach (var (recovered, method) in accepted)
            if (!problems.ContainsKey(recovered)) Write(ReadabilityRewriter.Rewrite(recovered, types, readability), method);
        return problems;
    }

    private string? Validate(ManagedBody recovered, MethodDefinition method, out ConstructorInitialization.Shape? shape)
    {
        shape = null;
        if (!method.HasBody) return "方法不允许 CIL 方法体";
        if (recovered.Blocks.Count == 0) return "空控制流图";
        var blockAddresses = recovered.Blocks.Select(b => b.Address).ToHashSet();
        if (blockAddresses.Count != recovered.Blocks.Count) return "控制流 块地址重复，无法唯一确定跳转标签";
        foreach (var edge in recovered.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges))
            if (!blockAddresses.Contains(edge.Target)) return $"控制流 跳转目标 0x{edge.Target:x} 不在方法体中";
        accessContext = recovered.Method.Method.Owner;
        methodContext = recovered.Method;
        if (method.IsConstructor && !method.IsStatic && !method.DeclaringType.IsValueType)
        {
            if (ConstructorInitialization.Check(recovered, out var constructorShape) is { } initializationProblem) return initializationProblem;
            shape = constructorShape;
        }
        foreach (var statement in recovered.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedCall c && !CanAccess(c.Invocation.Method, c.Invocation.Receiver?.Type))
                return $"访问权限 调用 {c.Invocation.Method}";
            if (statement is ManagedStore store && (StaticWriteProblem(store.Target) ?? ReadonlyWriteProblem(store.Target)) is { } writeProblem)
            {
                if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1") Console.Error.WriteLine($"  [写出问题] 0x{statement.Address:x} {statement}");
                return writeProblem;
            }
            if (statement is ManagedStore { Target: not (FieldValue or StaticFieldValue or ArrayElementValue or IndirectValue) }) return "写入位置不是字段或数组元素";
            if (statement is ManagedCheck check && !CanAccess(check.Exception, null)) return $"访问权限 异常构造 {check.Exception}";
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

    private string? Problem(ManagedValue value)
    {
        // async void 的完成标记不产生栈值，不能按普通值要求非零位宽。
        if (value is AsyncResultValue { Value: null } && ManagedTypes.IsVoid(value.Type)) return null;
        // 开放 T 的大小由 CLR 决定；仅保留有类型的复制、字段、局部和 default(T)。
        var genericStorage = value.Type is GenericParameterRef && value is LocalValue or FieldValue or IndirectValue or ComposedValue { Leaves.Count: 0 };
        if (value.Width is not (1 or 8 or 16 or 32 or 64) && !(value.Width == 0 && (types.Kind(value.Type) == TypeKind.Struct || genericStorage))) return $"位宽 {value.Width} 尚未支持";
        // C# 里每个值的类型都可能要按名写出（局部变量声明、转换）
        if (!CanAccess(value.Type)) return $"访问权限 类型 {value.Type}";
        switch (value)
        {
            case DelegateValue delegated:
                if (DelegateProblem(delegated) is { } delegateProblem) return delegateProblem;
                break;
            case StringValue: return value.Type.Equals(types.String) ? null : "字符串常量类型不符";
            case HoleValue: return null;
            case AsyncResultValue: break;
            case TypeHandleValue handle:
                if (!CanAccess(handle.Target)) return $"访问权限 类型 {handle.Target}";
                return handle.Type.Equals(types.RuntimeTypeHandle) ? null : "类型句柄的托管类型不符";
            case NewObjectValue created:
                var constructor = created.Constructor;
                if (constructor.Method.Name != ".ctor" || constructor.Method.IsStatic || constructor.Method.Parameters.Count != created.Arguments.Count)
                    return "构造 不是实例构造函数或参数个数不符";
                if (!CanAccess(constructor, created.Type)) return $"访问权限 构造 {constructor}";
                break;
            case NewArrayValue array:
                if (!array.ArrayType.IsVector) return "数组 分配需要一维向量类型";
                break;
            case BoxValue box:
                if (!CanAccess(box.Boxed)) return $"访问权限 类型 {box.Boxed}";
                if (box.Boxed is not GenericParameterRef && types.Kind(box.Boxed) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Struct)) return $"装箱 类型 {box.Boxed}";
                if (box.Boxed is DefinitionRef { Definition.FullName: "System.Nullable" }) return "装箱 Nullable 尚未支持";
                break;
            case UnboxAddressValue unbox:
                if (!CanAccess(unbox.Target)) return $"访问权限 类型 {unbox.Target}";
                if (unbox.Target is not (DefinitionRef { Definition.IsEnum: true } or GenericParameterRef { NativeScalar: not null })) return $"拆箱 类型 {unbox.Target} 尚未支持";
                break;
            case ArrayLengthValue length:
                if (length.Array.Type is not ArrayRef { IsVector: true }) return "数组 长度需要一维向量类型";
                break;
            case ArrayElementValue element:
                if (element.Array.Type is not ArrayRef { IsVector: true } a || !element.Type.Equals(a.Element)) return "数组 元素类型不符";
                break;
            case ConstantValue c:
                if (!(types.Kind(c.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double
                    || c.Bits == 0 && (ManagedTypes.IsReferenceType(c.Type) || ManagedTypes.IsNativePointer(c.Type))))
                    return $"常量 类型 {c.Type}";
                break;
            case ComposedValue c:
                foreach (var leaf in c.Leaves)
                    foreach (var field in leaf.Path)
                    {
                        if (!CanAccess(field, field.DeclaringType)) return $"访问权限 字段 {field}";
                        if (!IgnoreAccess && (field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
                            && !(methodContext.Method.Name == ".ctor" && methodContext.Method.Owner == field.Field.Owner))
                            return $"只读实例字段 不能逐叶子合成 {field.DeclaringType}：{field}";
                    }
                break;
            case AddressValue takenAddress:
                if (ReadonlyWriteProblem(takenAddress.Target) is { } readonlyProblem) return readonlyProblem;
                break;
            case FieldValue f:
                if (f.Accessor is { } instanceAccessor ? !instanceAccessor.Matches(types, accessContext, f, instanceAccessor.Write) : !CanAccess(f.Field, f.Receiver.Type)) return $"访问权限 字段 {f.Field}";
                return Problem(f.Receiver is AddressValue address ? address.Target : f.Receiver);
            case StaticFieldValue f:
                if (!f.Field.Field.IsStatic || (f.Field.Field.Attributes & System.Reflection.FieldAttributes.Literal) != 0)
                    return "静态字段 存储类型不符";
                if (f.Accessor is { } staticAccessor ? !staticAccessor.Matches(types, accessContext, f, staticAccessor.Write) : !CanAccess(f.Field, null)) return $"访问权限 静态字段 {f.Field}";
                break;
            case ConversionValue { Kind: ConvKind.Bitcast } bitcast
                when (types.Kind(bitcast.Operand.Type) is TypeKind.Float or TypeKind.Double) != (types.Kind(bitcast.Type) is TypeKind.Float or TypeKind.Double):
                // Reinterpret 用 stloc/ldloca/ldobj 换类型读取，ILVerify 判为不可验证（float& 按 int 读取）。
                // 改用 BitConverter 并在执行对照中作为内建运算之前，不写出（F2 后续）
                return "转换 浮点与整数的位重解释尚未以可验证的 IL 写出";
            case BinaryValue b:
                if (b.Left.Width != b.Width || b.Right.Width != b.Width && b.Op is not (BinOp.Shl or BinOp.LShr or BinOp.AShr)) return "运算 位宽不一致";
                break;
            case ComparisonValue c:
                if (c.Condition is not (Cond.Eq or Cond.Ne or Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge or Cond.Ult or Cond.Ule or Cond.Ugt or Cond.Uge
                    or Cond.FEq or Cond.FUne or Cond.FLt or Cond.FLe or Cond.FGt or Cond.FGe or Cond.FUlt or Cond.FUle or Cond.FUgt or Cond.FUge))
                    return $"比较 {c.Condition} 尚未支持";
                break;
        }
        foreach (var child in ManagedValues.Children(value))
            if (Problem(child) is { } problem) return problem;
        return null;
    }

    private string? StaticWriteProblem(ManagedValue target) =>
        !IgnoreAccess && target is StaticFieldValue storage && (storage.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(methodContext.Method is { Name: ".cctor", IsStatic: true } && methodContext.Method.Owner == storage.Field.Field.Owner)
            ? $"只读静态字段 只能在本类静态构造函数中写入: {storage.Field.Field}" : null;

    private void Write(ManagedBody recovered, MethodDefinition method)
    {
        destination = method;
        body = new MethodBody(method) { InitLocals = true };
        il = body.GetILProcessor();
        locals.Clear();
        labels.Clear();
        methodContext = recovered.Method;
        regions = recovered.Regions;
        exceptionReturn = null;
        exceptionReturnValue = null;
        foreach (var block in recovered.Blocks) labels.Add(block.Address, Instruction.Create(OpCodes.Nop));
        foreach (var block in recovered.Blocks)
        {
            currentBlock = block.Address;
            il.Append(labels[block.Address]);
            foreach (var region in regions.Where(r => r.HandlerEntry == block.Address && r.Kind == ManagedRegionKind.Catch))
                il.Emit(OpCodes.Stloc, Local(region.Exception!));
            foreach (var statement in block.Statements) Statement(statement);
        }
        WriteExceptionTable(recovered);
        method.Body = body;
    }

    private VariableDefinition Local(LocalValue value)
    {
        if (!locals.TryGetValue(value.Variable, out var local)) locals.Add(value.Variable, local = Temp(value.Type));
        return local;
    }

    private VariableDefinition Temp(TypeRef type)
    {
        var local = new VariableDefinition(TypeReference(type));
        body.Variables.Add(local);
        return local;
    }

}
