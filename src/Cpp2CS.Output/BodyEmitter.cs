using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Output;

/// <summary>把托管 CFG 写成 CIL；先检查支持范围，失败时保留原方法体。边赋值采用先读后写。</summary>
public sealed class BodyEmitter(ManagedTypes types, Func<TypeRef, TypeReference> typeReference,
    Func<FieldRef, FieldReference> fieldReference, Func<MethodRef, MethodReference> methodReference)
{
    private readonly Dictionary<Variable, VariableDefinition> locals = new();
    private readonly Dictionary<ulong, Instruction> labels = new();
    private MethodDefinition destination = null!;
    private MethodBody body = null!;
    private ILProcessor il = null!;
    private TypeDef accessContext = null!;

    public static string? Emit(Skeleton skeleton, ManagedTypes types, ManagedBody recovered)
    {
        var method = skeleton.Method(recovered.Method.Method);
        var emitter = new BodyEmitter(types,
            t => skeleton.Reference(method.Module, t, method.DeclaringType, method),
            f => skeleton.Reference(method.Module, f, method.DeclaringType, method),
            m => skeleton.Reference(method.Module, m, method.DeclaringType, method));
        return emitter.Emit(recovered, method);
    }

    public string? Emit(ManagedBody recovered, MethodDefinition method)
    {
        if (!method.HasBody) return "方法不允许 CIL 方法体";
        if (recovered.Method.TypeArguments.Count > 0 || recovered.Method.MethodArguments.Count > 0
            || recovered.Method.Method.GenericParameters.Count > 0 || recovered.Method.Method.Owner.GenericParameters.Count > 0)
            return "具体泛型实例尚未合并为开放方法体";
        if (recovered.Blocks.Count == 0) return "空控制流图";
        accessContext = recovered.Method.Method.Owner;
        if (method.IsConstructor && !method.IsStatic && !method.DeclaringType.IsValueType
            && !HasEntryConstructorCall(recovered)) return "引用类型构造函数的基类初始化尚未确认";
        foreach (var block in recovered.Blocks)
            foreach (var statement in block.Statements)
            {
                if (statement is ManagedCall c && !Accessible(c.Invocation.Method.Method.Owner,
                    (int)(c.Invocation.Method.Method.Attributes & SR.MethodAttributes.MemberAccessMask), c.Invocation.Receiver))
                    return $"调用访问权限尚未恢复: {c.Invocation.Method}";
                foreach (var value in Values(statement))
                    if (Problem(value) is { } problem) return problem;
            }

        destination = method;
        body = new MethodBody(method) { InitLocals = true };
        il = body.GetILProcessor();
        locals.Clear();
        labels.Clear();
        foreach (var block in recovered.Blocks) labels.Add(block.Address, Instruction.Create(OpCodes.Nop));
        foreach (var block in recovered.Blocks)
        {
            il.Append(labels[block.Address]);
            foreach (var statement in block.Statements) Statement(statement);
        }
        method.Body = body;
        return null;
    }

    // FieldAccessMask 与 MemberAccessMask 的 0..6 取值相同。Family 同时限制访问上下文与接收者类型。
    private bool Accessible(TypeDef owner, int access, ManagedValue? receiver)
    {
        var sameAssembly = owner.Assembly == accessContext.Assembly;
        var privateAccess = false;
        var familyAccess = false;
        for (var context = accessContext; context is not null; context = context.DeclaringType)
        {
            privateAccess |= context == owner;
            var contextType = new DefinitionRef(context, []);
            var receiverType = receiver?.Type is ByRefRef byRef ? byRef.Element : receiver?.Type;
            familyAccess |= types.IsAssignable(contextType, new DefinitionRef(owner, []))
                && (receiverType is null || types.IsAssignable(receiverType, contextType));
        }
        return access switch
        {
            6 => true, 1 => privateAccess, 2 => familyAccess && sameAssembly,
            3 => sameAssembly, 4 => familyAccess, 5 => familyAccess || sameAssembly,
            _ => false,
        };
    }

    private static bool HasEntryConstructorCall(ManagedBody recovered)
    {
        if (recovered.Blocks[0].Statements.FirstOrDefault() is not ManagedCall
            { Invocation: { Method: var target, Receiver: ArgumentValue { Index: -1 } } }) return false;
        var owner = recovered.Method.Method.Owner;
        return target.Method.Name == ".ctor" && !target.Method.IsStatic
            && (target.Method.Owner == owner || target.DeclaringType == owner.BaseType);
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
        if (value.Width is not (1 or 8 or 16 or 32 or 64)) return $"CIL 尚未支持位宽 {value.Width}";
        IEnumerable<ManagedValue> children;
        switch (value)
        {
            case ArgumentValue or LocalValue: return null;
            case ConstantValue c:
                return types.Kind(c.Type) is ValueKind.Int or ValueKind.Bool or ValueKind.Float or ValueKind.Double
                    || (c.Bits == 0 && ManagedTypes.IsReferenceType(c.Type)) ? null : "CIL 常量类型未支持";
            case FieldValue f:
                if (!Accessible(f.Field.Field.Owner, (int)(f.Field.Field.Attributes & SR.FieldAttributes.FieldAccessMask), f.Receiver))
                    return $"内联字段访问权限尚未恢复: {f.Field.Field}";
                children = [f.Receiver]; break;
            case IndirectValue i: children = [i.Address]; break;
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

    private void Statement(ManagedStatement statement)
    {
        switch (statement)
        {
            case ManagedAssignment a: Value(a.Value); il.Emit(OpCodes.Stloc, Local(a.Target)); break;
            case ManagedStore { Target: FieldValue f } s:
                Receiver(f.Receiver); Value(s.Value); il.Emit(OpCodes.Stfld, fieldReference(f.Field)); break;
            case ManagedStore { Target: IndirectValue i } s:
                Value(i.Address); Value(s.Value); il.Emit(OpCodes.Stobj, typeReference(i.Type)); break;
            case ManagedCall c:
                if (c.Invocation.Receiver is { } receiver) Receiver(receiver);
                foreach (var argument in c.Invocation.Arguments) Value(argument);
                il.Emit(OpCodes.Call, methodReference(c.Invocation.Method));
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

    private void Address(ManagedValue value)
    {
        switch (value)
        {
            case LocalValue local: il.Emit(OpCodes.Ldloca, Local(local)); break;
            case ArgumentValue { Index: >= 0 } argument: il.Emit(OpCodes.Ldarga, destination.Parameters[argument.Index]); break;
            case FieldValue field: Receiver(field.Receiver); il.Emit(OpCodes.Ldflda, fieldReference(field.Field)); break;
            case IndirectValue indirect: Value(indirect.Address); break;
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
            case ConstantValue c:
                if (ManagedTypes.IsReferenceType(c.Type)) il.Emit(OpCodes.Ldnull);
                else if (types.Kind(c.Type) == ValueKind.Float) il.Emit(OpCodes.Ldc_R4, BitConverter.Int32BitsToSingle(unchecked((int)c.Bits)));
                else if (types.Kind(c.Type) == ValueKind.Double) il.Emit(OpCodes.Ldc_R8, BitConverter.Int64BitsToDouble(unchecked((long)c.Bits)));
                else if (c.Width == 64) il.Emit(OpCodes.Ldc_I8, unchecked((long)c.Bits));
                else il.Emit(OpCodes.Ldc_I4, unchecked((int)c.Bits));
                break;
            case FieldValue f: Receiver(f.Receiver); il.Emit(OpCodes.Ldfld, fieldReference(f.Field)); break;
            case IndirectValue i: Value(i.Address); il.Emit(OpCodes.Ldobj, typeReference(i.Type)); break;
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
