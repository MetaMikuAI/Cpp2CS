using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>把托管 CFG 写成 CIL；先检查支持范围，失败时保留原方法体。边赋值采用先读后写。</summary>
public sealed class BodyEmitter(ManagedTypes types, Func<TypeRef, TypeReference> typeReference,
    Func<FieldRef, FieldReference> fieldReference, Func<MethodRef, MethodReference> methodReference)
{
    private readonly Dictionary<Variable, VariableDefinition> locals = new();
    private readonly Dictionary<long, VariableDefinition> stackLocals = new();
    private readonly Dictionary<ulong, Instruction> labels = new();
    private MethodDefinition destination = null!;
    private MethodBody body = null!;
    private ILProcessor il = null!;
    private TypeDef accessContext = null!;
    private MethodRef methodContext = null!;

    public static string? Emit(Skeleton skeleton, ManagedTypes types, ManagedBody recovered)
    {
        var pending = new List<(BodyEmitter Emitter, ManagedBody Body, MethodDefinition Method)>();
        foreach (var body in recovered.Accessors.Select(a => a.Proof.Body).Concat(recovered.Constructors.Select(c => c.Body)).Append(recovered).DistinctBy(b => b.Method))
        {
            var method = skeleton.Method(body.Method.Method);
            var emitter = new BodyEmitter(types,
                t => skeleton.Reference(method.Module, t, method.DeclaringType, method),
                f => skeleton.Reference(method.Module, f, method.DeclaringType, method),
                m => skeleton.Reference(method.Module, m, method.DeclaringType, method));
            if (emitter.Validate(body, method) is { } problem)
                return body == recovered ? problem : $"恢复依赖无法输出: {body.Method}: {problem}";
            pending.Add((emitter, body, method));
        }
        foreach (var item in pending) item.Emitter.Write(item.Body, item.Method);
        return null;
    }

    public string? Emit(ManagedBody recovered, MethodDefinition method)
    {
        if (Validate(recovered, method) is { } problem) return problem;
        Write(recovered, method);
        return null;
    }

    private string? Validate(ManagedBody recovered, MethodDefinition method)
    {
        if (!method.HasBody) return "方法不允许 CIL 方法体";
        if (recovered.Method.TypeArguments.Count > 0 || recovered.Method.MethodArguments.Count > 0
            || recovered.Method.Method.GenericParameters.Count > 0 || recovered.Method.Method.Owner.GenericParameters.Count > 0)
            return "具体泛型实例尚未合并为开放方法体";
        if (recovered.Blocks.Count == 0) return "空控制流图";
        accessContext = recovered.Method.Method.Owner;
        methodContext = recovered.Method;
        if (method.IsConstructor && !method.IsStatic && !method.DeclaringType.IsValueType
            && ConstructorInitialization.Check(recovered) is { } initializationProblem) return initializationProblem;
        foreach (var block in recovered.Blocks)
            foreach (var statement in block.Statements)
            {
                if (statement is ManagedCall c && !ManagedAccess.Method(types, accessContext, c.Invocation.Method, c.Invocation.Receiver?.Type))
                    return $"调用访问权限尚未恢复: {c.Invocation.Method}";
                if (statement is ManagedStore store && StaticWriteProblem(store.Target) is { } writeProblem) return writeProblem;
                if (statement is ManagedCall { Invocation.Receiver: { } receiver } && types.Kind(receiver.Type) == ValueKind.Struct
                    && StaticWriteProblem(receiver) is { } receiverProblem) return receiverProblem;
                foreach (var value in Values(statement))
                    if (Problem(value) is { } problem) return problem;
            }
        return null;
    }

    private void Write(ManagedBody recovered, MethodDefinition method)
    {
        destination = method;
        body = new MethodBody(method) { InitLocals = true };
        il = body.GetILProcessor();
        locals.Clear();
        stackLocals.Clear();
        labels.Clear();
        foreach (var block in recovered.Blocks) labels.Add(block.Address, Instruction.Create(OpCodes.Nop));
        foreach (var block in recovered.Blocks)
        {
            il.Append(labels[block.Address]);
            foreach (var statement in block.Statements) Statement(statement);
        }
        method.Body = body;
    }

    private static IEnumerable<ManagedValue> Values(ManagedStatement statement) => statement switch
    {
        ManagedAssignment a => [a.Target, a.Value],
        ManagedStore s => [s.Target, s.Value],
        ManagedCall c => (c.Invocation.Receiver is { } receiver ? new[] { receiver } : []).Concat(c.Invocation.Arguments),
        ManagedReturn { Value: { } value } => [value],
        ManagedJump j => j.Edge.Copies.SelectMany(c => new ManagedValue[] { c.Target, c.Value }),
        ManagedBranch b => new[] { b.Condition }.Concat(b.Taken.Copies.Concat(b.Fallthrough.Copies).SelectMany(c => new ManagedValue[] { c.Target, c.Value })),
        ManagedReturn => [],
        _ => throw new NotSupportedException(statement.ToString()),
    };

    private string? Problem(ManagedValue value)
    {
        if (value.Width is not (1 or 8 or 16 or 32 or 64) && types.Kind(value.Type) != ValueKind.Struct) return $"CIL 尚未支持位宽 {value.Width}";
        IEnumerable<ManagedValue> children;
        switch (value)
        {
            case ArgumentValue or LocalValue or StackLocalValue: return null;
            case StringValue: return value.Type == types.String ? null : "字符串常量类型不符";
            case TypeHandleValue handle: return handle.Type == types.RuntimeTypeHandle && handle.Width == types.Size(types.RuntimeTypeHandle) * 8
                ? null : "类型句柄的托管类型不符";
            case NewArrayValue array:
                if (!array.ArrayType.IsVector || array.ArrayType.Rank != 1) return "数组分配需要 SZARRAY 类型";
                children = [array.Length]; break;
            case BoxValue box:
                if (box.Type != types.Object || !types.CanBox(box.Operand.Type) || box.Operand.Width != types.Size(box.Operand.Type) * 8)
                    return "装箱值的类型或位宽不符";
                var initialization = Boxing.Initialization(types, box.Operand.Type, out var initializationProblem);
                if (initializationProblem is not null) return initializationProblem;
                if (box.Initialization != initialization) return "装箱的类初始化顺序尚未确认";
                children = [box.Operand]; break;
            case ArrayLengthValue length:
                if (length.Array.Type is not ArrayRef { Rank: 1, IsVector: true }) return "数组长度需要 SZARRAY 类型";
                children = [length.Array]; break;
            case ArrayElementValue element:
                if (element.Array.Type is not ArrayRef { Rank: 1, IsVector: true } a || element.Type != a.Element) return "数组元素类型不符";
                children = [element.Array, element.Index]; break;
            case DefaultValue: return types.Kind(value.Type) == ValueKind.Struct ? null : "default 值必须为已知结构体";
            case AddressValue reference:
                if (StaticWriteProblem(reference.Target) is { } addressProblem) return addressProblem;
                children = [reference.Target]; break;
            case AggregateValue aggregate:
                foreach (var member in aggregate.Members)
                {
                    var receiverType = aggregate.Type;
                    foreach (var field in member.Path)
                    {
                        if ((field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0) return $"只读聚合字段的非零初始化尚未恢复: {field.Field}";
                        if (!ManagedAccess.Field(types, accessContext, field, receiverType)) return $"聚合字段访问权限尚未恢复: {field.Field}";
                        receiverType = field.Field.Type.Substitute(field.DeclaringType is DefinitionRef d ? d.Arguments : [], []);
                    }
                }
                children = aggregate.Members.Select(m => m.Value); break;
            case ConstantValue c:
                return types.Kind(c.Type) is ValueKind.Int or ValueKind.Bool or ValueKind.Float or ValueKind.Double
                    || (c.Bits == 0 && ManagedTypes.IsReferenceType(c.Type)) ? null : "CIL 常量类型未支持";
            case FieldValue f:
                if (!ManagedAccess.Field(types, accessContext, f.Field, f.Receiver.Type))
                    return $"内联字段访问权限尚未恢复: {f.Field.Field}";
                children = [f.Receiver]; break;
            case StaticFieldValue f:
                if (!f.Field.Field.IsStatic || f.Field.Field.IsThreadStatic
                    || (f.Field.Field.Attributes & System.Reflection.FieldAttributes.Literal) != 0) return "静态字段存储类型不符";
                if (f.Type != f.Field.Field.Type.Substitute(f.Field.DeclaringType is DefinitionRef declaring ? declaring.Arguments : [], [])
                    || f.Width != types.Size(f.Type) * 8) return "静态字段值类型或位宽不符";
                return ManagedAccess.Field(types, accessContext, f.Field, null) ? null : $"静态字段访问权限尚未恢复: {f.Field.Field}";
            case IndirectValue i: children = [i.Address]; break;
            case InvocationValue invocation:
                if (!ManagedAccess.Method(types, accessContext, invocation.Invocation.Method, invocation.Invocation.Receiver?.Type))
                    return $"调用访问权限尚未恢复: {invocation.Invocation.Method}";
                if (invocation.Invocation.Receiver is { } target && types.Kind(target.Type) == ValueKind.Struct
                    && StaticWriteProblem(target) is { } targetProblem) return targetProblem;
                children = invocation.Invocation.Receiver is { } receiver
                    ? new[] { receiver }.Concat(invocation.Invocation.Arguments) : invocation.Invocation.Arguments;
                break;
            case BinaryValue b:
                if (b.Op is not (BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr
                    or BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv)) return $"CIL 运算尚未支持 {b.Op}";
                if (b.Left.Width != b.Width || (b.Right.Width != b.Width && b.Op is not (BinOp.Shl or BinOp.LShr or BinOp.AShr))) return "CIL 运算位宽不一致";
                children = [b.Left, b.Right]; break;
            case UnaryValue u:
                if (u.Op is not (UnOp.Neg or UnOp.Not or UnOp.FNeg)) return $"CIL 运算尚未支持 {u.Op}";
                children = [u.Operand]; break;
            case ConversionValue c:
                if (c.Kind is ConvKind.FloatToSInt or ConvKind.FloatToUInt) return "浮点转整数的饱和语义尚未实现";
                if (c.Kind == ConvKind.Bitcast && c.Width != c.Operand.Width) return "位重解释宽度不符";
                children = [c.Operand]; break;
            case ComparisonValue c:
                if (c.Condition is not (Cond.Eq or Cond.Ne or Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge or Cond.Ult or Cond.Ule or Cond.Ugt or Cond.Uge
                    or Cond.FEq or Cond.FUne or Cond.FLt or Cond.FLe or Cond.FGt or Cond.FGe or Cond.FUlt or Cond.FUle or Cond.FUgt or Cond.FUge))
                    return $"CIL 比较尚未支持 {c.Condition}";
                if (c.Left.Width != c.Right.Width) return "比较位宽不一致";
                children = [c.Left, c.Right]; break;
            case ChoiceValue c: children = [c.Condition, c.True, c.False]; break;
            case BooleanValue b: children = [b.Left, b.Right]; break;
            case NegatedValue n: children = [n.Operand]; break;
            default: return $"CIL 值尚未支持 {value.GetType().Name}";
        }
        foreach (var child in children)
            if (Problem(child) is { } problem) return problem;
        return null;
    }

    private string? StaticWriteProblem(ManagedValue target)
    {
        FieldRef? readOnlyMember = null;
        while (target is FieldValue field && types.Kind(field.Receiver.Type) == ValueKind.Struct)
        {
            if ((field.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0) readOnlyMember = field.Field;
            target = field.Receiver;
        }
        if (target is not StaticFieldValue storage) return null;
        if (readOnlyMember is not null) return $"静态存储内只读结构体字段的写入尚未恢复: {readOnlyMember.Field}";
        return (storage.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(methodContext.Method is { Name: ".cctor", IsStatic: true } && methodContext.Method.Owner == storage.Field.Field.Owner)
                ? $"只读静态字段只能在本类静态构造函数中写入或传递可写引用: {storage.Field.Field}" : null;
    }

    private VariableDefinition Local(LocalValue value)
    {
        if (!locals.TryGetValue(value.Variable, out var local)) locals.Add(value.Variable, local = Temp(value.Type));
        return local;
    }

    private VariableDefinition Temp(TypeRef type)
    {
        var local = new VariableDefinition(typeReference(type));
        body.Variables.Add(local);
        return local;
    }

    private VariableDefinition StackLocal(StackLocalValue value)
    {
        if (!stackLocals.TryGetValue(value.Offset, out var local)) stackLocals.Add(value.Offset, local = Temp(value.Type));
        return local;
    }

    private void Statement(ManagedStatement statement)
    {
        switch (statement)
        {
            case ManagedAssignment a: Value(a.Value); il.Emit(OpCodes.Stloc, Local(a.Target)); break;
            case ManagedStore { Target: StackLocalValue local } s: Value(s.Value); il.Emit(OpCodes.Stloc, StackLocal(local)); break;
            case ManagedStore { Target: FieldValue f } s:
                Receiver(f.Receiver); Value(s.Value); il.Emit(OpCodes.Stfld, fieldReference(f.Field)); break;
            case ManagedStore { Target: StaticFieldValue f } s:
                Value(s.Value); il.Emit(OpCodes.Stsfld, fieldReference(f.Field)); break;
            case ManagedStore { Target: IndirectValue i } s:
                Value(i.Address); Value(s.Value); il.Emit(OpCodes.Stobj, typeReference(i.Type)); break;
            case ManagedStore { Target: ArrayElementValue element } s:
                Value(element.Array); Value(element.Index); il.Emit(OpCodes.Conv_U); Value(s.Value);
                il.Emit(OpCodes.Stelem_Any, typeReference(element.Type)); break;
            case ManagedCall c:
                Invocation(c.Invocation);
                if (c.Tail) il.Emit(OpCodes.Ret);
                else if (c.Result is { } result) il.Emit(OpCodes.Stloc, Local(result));
                break;
            case ManagedReturn r:
                if (r.Value is { } returned) Value(returned);
                il.Emit(OpCodes.Ret); break;
            case ManagedJump j: Edge(j.Edge); break;
            case ManagedBranch b:
                var taken = Instruction.Create(OpCodes.Nop);
                Value(b.Condition); il.Emit(OpCodes.Brtrue, taken);
                Edge(b.Fallthrough);
                il.Append(taken); Edge(b.Taken); break;
            default: throw new NotSupportedException(statement.ToString());
        }
    }

    private void Edge(ManagedEdge edge)
    {
        foreach (var copy in edge.Copies) Value(copy.Value);
        for (var i = edge.Copies.Count - 1; i >= 0; i--) il.Emit(OpCodes.Stloc, Local(edge.Copies[i].Target));
        il.Emit(OpCodes.Br, labels[edge.Target]);
    }

    private void Receiver(ManagedValue value)
    {
        if (types.Kind(value.Type) == ValueKind.Struct) Address(value);
        else Value(value);
    }

    private void Invocation(ManagedInvocation invocation)
    {
        if (invocation.Receiver is { } receiver) Receiver(receiver);
        foreach (var argument in invocation.Arguments) Value(argument);
        il.Emit(OpCodes.Call, methodReference(invocation.Method));
    }

    private void Address(ManagedValue value)
    {
        switch (value)
        {
            case LocalValue local: il.Emit(OpCodes.Ldloca, Local(local)); break;
            case StackLocalValue local: il.Emit(OpCodes.Ldloca, StackLocal(local)); break;
            case ArgumentValue { Index: >= 0 } argument: il.Emit(OpCodes.Ldarga, destination.Parameters[argument.Index]); break;
            case FieldValue field: Receiver(field.Receiver); il.Emit(OpCodes.Ldflda, fieldReference(field.Field)); break;
            case StaticFieldValue field: il.Emit(OpCodes.Ldsflda, fieldReference(field.Field)); break;
            case IndirectValue indirect: Value(indirect.Address); break;
            case ArrayElementValue element:
                Value(element.Array); Value(element.Index); il.Emit(OpCodes.Conv_U); il.Emit(OpCodes.Ldelema, typeReference(element.Type)); break;
            case InvocationValue invocation:
                Value(invocation);
                var temp = Temp(invocation.Type);
                il.Emit(OpCodes.Stloc, temp); il.Emit(OpCodes.Ldloca, temp); break;
            default: throw new NotSupportedException($"不可取地址的值 {value}");
        }
    }

    private void Value(ManagedValue value)
    {
        switch (value)
        {
            case ArgumentValue a:
                if (a.Index == -1) il.Emit(OpCodes.Ldarg_0);
                else il.Emit(OpCodes.Ldarg, destination.Parameters[a.Index]);
                break;
            case LocalValue l: il.Emit(OpCodes.Ldloc, Local(l)); break;
            case StackLocalValue l: il.Emit(OpCodes.Ldloc, StackLocal(l)); break;
            case AddressValue reference: Address(reference.Target); break;
            case DefaultValue empty:
                var initialized = Temp(empty.Type);
                il.Emit(OpCodes.Ldloca, initialized); il.Emit(OpCodes.Initobj, typeReference(empty.Type));
                il.Emit(OpCodes.Ldloc, initialized); break;
            case AggregateValue aggregate:
                var constructed = Temp(aggregate.Type);
                il.Emit(OpCodes.Ldloca, constructed); il.Emit(OpCodes.Initobj, typeReference(aggregate.Type));
                foreach (var member in aggregate.Members)
                {
                    il.Emit(OpCodes.Ldloca, constructed);
                    foreach (var field in member.Path.SkipLast(1)) il.Emit(OpCodes.Ldflda, fieldReference(field));
                    Value(member.Value); il.Emit(OpCodes.Stfld, fieldReference(member.Path[^1]));
                }
                il.Emit(OpCodes.Ldloc, constructed); break;
            case ConstantValue c:
                if (ManagedTypes.IsReferenceType(c.Type)) il.Emit(OpCodes.Ldnull);
                // C# 的 NaN 字面表示不保留符号和载荷；以整数位型输出，避免源码往返时被规范化。
                else if (types.Kind(c.Type) == ValueKind.Float && (c.Bits & 0x7f800000) == 0x7f800000 && (c.Bits & 0x7fffff) != 0)
                {
                    il.Emit(OpCodes.Ldc_I4, unchecked((int)c.Bits)); Reinterpret(types.UInt32, c.Type);
                }
                else if (types.Kind(c.Type) == ValueKind.Double && (c.Bits & 0x7ff0000000000000) == 0x7ff0000000000000 && (c.Bits & 0xfffffffffffff) != 0)
                {
                    il.Emit(OpCodes.Ldc_I8, unchecked((long)c.Bits)); Reinterpret(types.UInt64, c.Type);
                }
                else if (types.Kind(c.Type) == ValueKind.Float) il.Emit(OpCodes.Ldc_R4, BitConverter.Int32BitsToSingle(unchecked((int)c.Bits)));
                else if (types.Kind(c.Type) == ValueKind.Double) il.Emit(OpCodes.Ldc_R8, BitConverter.Int64BitsToDouble(unchecked((long)c.Bits)));
                else if (c.Width == 64) il.Emit(OpCodes.Ldc_I8, unchecked((long)c.Bits));
                else il.Emit(OpCodes.Ldc_I4, unchecked((int)c.Bits));
                break;
            case StringValue text: il.Emit(OpCodes.Ldstr, text.Text); break;
            case BoxValue box: Box(box); break;
            case TypeHandleValue handle: il.Emit(OpCodes.Ldtoken, typeReference(handle.TargetType)); break;
            case NewArrayValue array:
                Value(array.Length); il.Emit(OpCodes.Conv_U); il.Emit(OpCodes.Newarr, typeReference(array.ArrayType.Element)); break;
            case ArrayLengthValue length:
                Value(length.Array); il.Emit(OpCodes.Ldlen); il.Emit(length.Width == 64 ? OpCodes.Conv_U8 : OpCodes.Conv_U4); break;
            case ArrayElementValue element:
                Value(element.Array); Value(element.Index); il.Emit(OpCodes.Conv_U); il.Emit(OpCodes.Ldelem_Any, typeReference(element.Type)); break;
            case FieldValue f: Receiver(f.Receiver); il.Emit(OpCodes.Ldfld, fieldReference(f.Field)); break;
            case StaticFieldValue f: il.Emit(OpCodes.Ldsfld, fieldReference(f.Field)); break;
            case IndirectValue i: Value(i.Address); il.Emit(OpCodes.Ldobj, typeReference(i.Type)); break;
            case InvocationValue invocation: Invocation(invocation.Invocation); break;
            case BinaryValue b: Binary(b); break;
            case UnaryValue u:
                if (u.Op == UnOp.FNeg) Floating(u.Operand); else Integer(u.Operand, false);
                il.Emit(u.Op == UnOp.Not ? OpCodes.Not : OpCodes.Neg);
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

    private void Box(BoxValue box)
    {
        if (box.Initialization is not { } initialize)
        {
            Value(box.Operand); il.Emit(OpCodes.Box, typeReference(box.Operand.Type)); return;
        }
        // 地址先固定，初始化后再读取；静态构造函数可能修改原存储。
        var pointer = Temp(new ByRefRef(box.Operand.Type));
        if (box.Operand is LocalValue or StackLocalValue or ArgumentValue or FieldValue or StaticFieldValue or IndirectValue or ArrayElementValue or InvocationValue)
            Address(box.Operand);
        else
        {
            var copy = Temp(box.Operand.Type); Value(box.Operand); il.Emit(OpCodes.Stloc, copy); il.Emit(OpCodes.Ldloca, copy);
        }
        il.Emit(OpCodes.Stloc, pointer);
        var empty = Instruction.Create(OpCodes.Ldnull);
        var end = Instruction.Create(OpCodes.Nop);
        if (initialize.HasValue is { } hasValue)
        {
            il.Emit(OpCodes.Ldloc, pointer); il.Emit(OpCodes.Call, methodReference(hasValue)); il.Emit(OpCodes.Brfalse, empty);
        }
        // 原生先分配，再初始化类型，最后复制数据；用一次空值装箱保留分配和异常的先后关系。
        var initial = Temp(initialize.TargetType);
        var allocated = Temp(types.Object);
        il.Emit(OpCodes.Ldloca, initial); il.Emit(OpCodes.Initobj, typeReference(initialize.TargetType));
        il.Emit(OpCodes.Ldloc, initial); il.Emit(OpCodes.Box, typeReference(initialize.TargetType)); il.Emit(OpCodes.Stloc, allocated);
        il.Emit(OpCodes.Ldtoken, typeReference(initialize.TargetType)); il.Emit(OpCodes.Call, methodReference(initialize.RunClassConstructor));
        il.Emit(OpCodes.Ldloc, allocated); il.Emit(OpCodes.Unbox, typeReference(initialize.TargetType));
        il.Emit(OpCodes.Ldloc, pointer);
        if (initialize.GetValueOrDefault is { } getValue) il.Emit(OpCodes.Call, methodReference(getValue));
        else il.Emit(OpCodes.Ldobj, typeReference(box.Operand.Type));
        il.Emit(OpCodes.Stobj, typeReference(initialize.TargetType)); il.Emit(OpCodes.Ldloc, allocated);
        if (initialize.HasValue is not null)
        {
            il.Emit(OpCodes.Br, end); il.Append(empty); il.Append(end);
        }
    }

    private void Binary(BinaryValue b)
    {
        if (types.Kind(b.Type) is ValueKind.Float or ValueKind.Double) { Floating(b.Left); Floating(b.Right); }
        else
        {
            Integer(b.Left, b.Op == BinOp.AShr);
            Integer(b.Right, false);
            if (b.Op is BinOp.Shl or BinOp.LShr or BinOp.AShr)
            {
                il.Emit(OpCodes.Conv_I4); il.Emit(OpCodes.Ldc_I4, b.Width - 1); il.Emit(OpCodes.And);
            }
        }
        il.Emit(b.Op switch
        {
            BinOp.Add or BinOp.FAdd => OpCodes.Add, BinOp.Sub or BinOp.FSub => OpCodes.Sub,
            BinOp.Mul or BinOp.FMul => OpCodes.Mul, BinOp.FDiv => OpCodes.Div,
            BinOp.And => OpCodes.And, BinOp.Or => OpCodes.Or, BinOp.Xor => OpCodes.Xor,
            BinOp.Shl => OpCodes.Shl, BinOp.LShr => OpCodes.Shr_Un, BinOp.AShr => OpCodes.Shr,
            _ => throw new NotSupportedException(b.Op.ToString()),
        });
        Normalize(b);
    }

    private void Conversion(ConversionValue c)
    {
        switch (c.Kind)
        {
            case ConvKind.Bitcast:
                if (c.Operand is ConstantValue constant)
                {
                    Value(new ConstantValue(constant.Bits, c.Type, c.Width));
                    break;
                }
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
            default: throw new NotSupportedException(c.Kind.ToString());
        }
    }

    private void Comparison(ComparisonValue c)
    {
        var floating = c.Condition is Cond.FEq or Cond.FUne or Cond.FLt or Cond.FLe or Cond.FGt or Cond.FGe or Cond.FUlt or Cond.FUle or Cond.FUgt or Cond.FUge;
        if (ManagedTypes.IsReferenceType(c.Left.Type)) { Value(c.Left); Value(c.Right); }
        else if (floating) { Floating(c.Left); Floating(c.Right); }
        else
        {
            var signed = c.Condition is Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge;
            Integer(c.Left, signed); Integer(c.Right, signed);
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
        if (types.Kind(value.Type) is ValueKind.Float or ValueKind.Double) Reinterpret(value.Type, types.Integer(value.Width, signed));
        IntegerWidth(value.Width, signed);
    }

    private void Floating(ManagedValue value)
    {
        Value(value);
        if (types.Kind(value.Type) is not (ValueKind.Float or ValueKind.Double))
            Reinterpret(value.Type, value.Width == 32 ? types.Single : types.Double);
    }

    private void Reinterpret(TypeRef from, TypeRef to)
    {
        var fromFloat = types.Kind(from) is ValueKind.Float or ValueKind.Double;
        var toFloat = types.Kind(to) is ValueKind.Float or ValueKind.Double;
        if (fromFloat == toFloat) return;
        var local = Temp(from);
        il.Emit(OpCodes.Stloc, local); il.Emit(OpCodes.Ldloca, local); il.Emit(OpCodes.Ldobj, typeReference(to));
    }

    private void Normalize(ManagedValue value)
    {
        if (types.Kind(value.Type) is ValueKind.Float or ValueKind.Double) il.Emit(value.Width == 32 ? OpCodes.Conv_R4 : OpCodes.Conv_R8);
        else IntegerWidth(value.Width, types.IsSigned(value.Type));
    }

    private void IntegerWidth(int width, bool signed)
    {
        if (width == 1) { il.Emit(OpCodes.Conv_I4); il.Emit(OpCodes.Ldc_I4_1); il.Emit(OpCodes.And); return; }
        il.Emit((width, signed) switch
        {
            (8, true) => OpCodes.Conv_I1, (8, false) => OpCodes.Conv_U1,
            (16, true) => OpCodes.Conv_I2, (16, false) => OpCodes.Conv_U2,
            (32, true) => OpCodes.Conv_I4, (32, false) => OpCodes.Conv_U4,
            (64, true) => OpCodes.Conv_I8, (64, false) => OpCodes.Conv_U8,
            _ => throw new NotSupportedException($"整数宽度 {width}"),
        });
    }

    private void Invert() { il.Emit(OpCodes.Ldc_I4_0); il.Emit(OpCodes.Ceq); }
}
