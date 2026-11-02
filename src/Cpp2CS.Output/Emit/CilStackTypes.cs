using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Collections.Generic;

namespace Cpp2CS.Output;

/// <summary>
/// 写出体的求值栈类型检查（ECMA-335 I.12.3.2.1、III.1.5、III.1.6、III.1.8.1.3）：逐条模拟栈上的中间类型，
/// 检查运算、比较、转换与分支的操作数，实参、存储与返回值的隐式转换，以及合流处的栈形状。
/// 只检查中间类型的类别与值类型的身份，不检查引用类型之间的可赋值性；泛型参数视为任意类型。
/// </summary>
internal static class CilStackTypes
{
    private enum Kind : byte { Int32, Int64, NativeInt, Float, Object, Reference, Value, Any }

    private readonly record struct Slot(Kind Kind, string? Value = null)
    {
        public override string ToString() => Kind switch
        {
            Kind.Int32 => "int32",
            Kind.Int64 => "int64",
            Kind.NativeInt => "native int",
            Kind.Float => "F",
            Kind.Object => "O",
            Kind.Reference => "&",
            Kind.Value => $"valuetype {Value}",
            _ => "*",
        };
    }

    private static readonly Slot I4 = new(Kind.Int32), I8 = new(Kind.Int64), I = new(Kind.NativeInt), F = new(Kind.Float),
        O = new(Kind.Object), Ref = new(Kind.Reference), Any = new(Kind.Any);

    /// <summary>第一处不一致的说明；一致时为 null。</summary>
    public static string? Check(MethodDefinition method, MethodBody body)
    {
        if (body.Instructions.Count == 0) return null;
        var states = new Dictionary<Instruction, Slot[]>();
        var work = new Stack<Instruction>();
        string? Merge(Instruction target, IReadOnlyList<Slot> stack, Instruction from)
        {
            if (!states.TryGetValue(target, out var known))
            {
                states[target] = stack.ToArray();
                work.Push(target);
                return null;
            }
            if (known.Length != stack.Count) return $"栈类型 IL_{target.Offset:x4} 合流处栈深度不一致：{known.Length} 与 {stack.Count}（来自 IL_{from.Offset:x4}）";
            for (var i = 0; i < known.Length; i++)
                if (Join(known[i], stack[i]) is not { } joined)
                    return $"栈类型 IL_{target.Offset:x4} 合流处栈类型不一致：{known[i]} 与 {stack[i]}（来自 IL_{from.Offset:x4}）";
                else if (joined != known[i]) { known[i] = joined; work.Push(target); }
            return null;
        }
        Renumber(body);
        if (Merge(body.Instructions[0], [], body.Instructions[0]) is { } entry) return entry;
        foreach (var handler in body.ExceptionHandlers)
        {
            Slot[] start = handler.HandlerType is ExceptionHandlerType.Catch or ExceptionHandlerType.Filter ? [O] : [];
            if (Merge(handler.HandlerStart, start, handler.HandlerStart) is { } problem) return problem;
            if (handler.HandlerType == ExceptionHandlerType.Filter && Merge(handler.FilterStart, [O], handler.FilterStart) is { } filter) return filter;
        }
        var index = body.Instructions.Select((ins, i) => (ins, i)).ToDictionary(p => p.ins, p => p.i);
        while (work.Count > 0)
        {
            var instruction = work.Pop();
            var stack = states[instruction].ToList();
            var simulator = new Simulator(method, body, instruction, stack);
            var (targets, falls) = simulator.Step();
            if (simulator.Error is { } error) return $"栈类型 IL_{instruction.Offset:x4} {instruction.OpCode.Name}：{error}";
            foreach (var target in targets)
                if (Merge(target, instruction.OpCode.Code is Code.Leave or Code.Leave_S ? [] : stack, instruction) is { } problem) return problem;
            if (!falls) continue;
            if (index[instruction] + 1 >= body.Instructions.Count) return $"栈类型 IL_{instruction.Offset:x4} 执行越过方法体末尾";
            if (Merge(body.Instructions[index[instruction] + 1], stack, instruction) is { } next) return next;
        }
        return null;
    }

    private static void Renumber(MethodBody body)
    {
        var offset = 0;
        foreach (var instruction in body.Instructions)
        {
            instruction.Offset = offset;
            offset += instruction.GetSize();
        }
    }

    /// <summary>合流：类别相同；值类型身份相同；任意类型与任何类型合流为另一方。</summary>
    private static Slot? Join(Slot a, Slot b)
    {
        if (a.Kind == Kind.Any) return b;
        if (b.Kind == Kind.Any) return a;
        if (a.Kind != b.Kind) return null;
        return a.Kind != Kind.Value || a.Value == b.Value ? a : null;
    }

    /// <summary>值 value 隐式转换为 target 类型的位置（III.1.6）。</summary>
    private static bool Assignable(Slot value, Slot target) => (target.Kind, value.Kind) switch
    {
        (Kind.Any, _) or (_, Kind.Any) => true,
        (Kind.Int32, Kind.Int32 or Kind.NativeInt) => true,
        (Kind.NativeInt, Kind.Int32 or Kind.NativeInt or Kind.Reference) => true,
        (Kind.Reference, Kind.Reference or Kind.NativeInt) => true,
        (Kind.Value, Kind.Value) => target.Value == value.Value,
        var (t, v) => t == v,
    };

    /// <summary>类型对应的中间类型（I.12.3.2.1）；void 为 null。</summary>
    private static Slot? Classify(TypeReference type)
    {
        while (type is IModifierType modifier) type = modifier.ElementType;
        switch (type)
        {
            case PinnedType pinned: return Classify(pinned.ElementType);
            case ByReferenceType: return Ref;
            case PointerType or FunctionPointerType: return I;
            case ArrayType: return O;
            case GenericParameter or SentinelType: return Any;
            case GenericInstanceType instance: return IsValueType(instance.ElementType) is { } value ? value ? new Slot(Kind.Value, instance.ElementType.FullName) : O : Any;
        }
        switch (type.FullName)
        {
            case "System.Void": return null;
            case "System.Boolean" or "System.Char" or "System.SByte" or "System.Byte" or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32": return I4;
            case "System.Int64" or "System.UInt64": return I8;
            case "System.IntPtr" or "System.UIntPtr": return I;
            case "System.Single" or "System.Double": return F;
        }
        if (type.Resolve() is not { } definition) return Any;
        if (definition.IsEnum) return Classify(definition.Fields.First(f => !f.IsStatic).FieldType);
        return definition.IsValueType ? new Slot(Kind.Value, definition.FullName) : O;
    }

    private static bool? IsValueType(TypeReference type) => type.Resolve()?.IsValueType;

    /// <summary>成员签名中的类型代入声明类型与泛型方法的实参。</summary>
    private static TypeReference Substitute(TypeReference type, MemberReference member)
    {
        while (type is IModifierType modifier) type = modifier.ElementType;
        if (type is not GenericParameter parameter) return type;
        Collection<TypeReference>? arguments = parameter.Type == GenericParameterType.Type
            ? (member.DeclaringType as GenericInstanceType)?.GenericArguments
            : (member as GenericInstanceMethod)?.GenericArguments;
        return arguments is not null && parameter.Position < arguments.Count ? arguments[parameter.Position] : type;
    }

    /// <summary>一条指令的栈效果；只保留第一处不一致。</summary>
    private sealed class Simulator(MethodDefinition method, MethodBody body, Instruction instruction, List<Slot> stack)
    {
        public string? Error { get; private set; }

        private void Fail(string message) => Error ??= message;

        private Slot Pop()
        {
            if (stack.Count == 0) { Fail("栈下溢"); return Any; }
            var top = stack[^1];
            stack.RemoveAt(stack.Count - 1);
            return top;
        }

        private void Push(Slot slot) => stack.Add(slot);

        private Slot Of(TypeReference type)
        {
            if (Classify(type) is { } slot) return slot;
            Fail("void 不能作为值");
            return Any;
        }

        private void Expect(Slot value, Slot target, string what)
        {
            if (!Assignable(value, target)) Fail($"{what}期望 {target}，栈上为 {value}");
        }

        private Slot PopInto(TypeReference type, string what)
        {
            var value = Pop();
            Expect(value, Of(type), what);
            return value;
        }

        private void PopOneOf(string what, params Kind[] kinds)
        {
            var value = Pop();
            if (value.Kind != Kind.Any && !kinds.Contains(value.Kind)) Fail($"{what}不能是 {value}");
        }

        private TypeReference Argument(int index)
        {
            if (method.HasThis)
            {
                if (index == 0) return body.ThisParameter.ParameterType;
                index--;
            }
            return method.Parameters[index].ParameterType;
        }

        private TypeReference Argument(ParameterDefinition parameter) =>
            ReferenceEquals(parameter, body.ThisParameter) ? body.ThisParameter.ParameterType : parameter.ParameterType;

        /// <summary>数值运算（III.1.5 表 III.2）；integer 时为整数运算（表 III.5），不接受 F 与托管指针。</summary>
        private void Numeric(bool integer, bool address)
        {
            var right = Pop();
            var left = Pop();
            if (left.Kind == Kind.Any || right.Kind == Kind.Any) { Push(left.Kind == Kind.Any ? right : left); return; }
            Slot? result = (left.Kind, right.Kind) switch
            {
                (Kind.Int32, Kind.Int32) => I4,
                (Kind.Int32 or Kind.NativeInt, Kind.Int32 or Kind.NativeInt) => I,
                (Kind.Int64, Kind.Int64) => I8,
                (Kind.Float, Kind.Float) when !integer => F,
                (Kind.Reference, Kind.Int32 or Kind.NativeInt) when address => Ref,
                (Kind.Int32 or Kind.NativeInt, Kind.Reference) when address && instruction.OpCode.Code == Code.Add => Ref,
                (Kind.Reference, Kind.Reference) when address && instruction.OpCode.Code == Code.Sub => I,
                _ => null,
            };
            if (result is null) Fail($"操作数 {left} 与 {right} 不能运算");
            Push(result ?? Any);
        }

        /// <summary>比较（表 III.4）；对象引用只能判等或与 null 做无符号比较。</summary>
        private void Compare(bool equality)
        {
            var right = Pop();
            var left = Pop();
            var valid = (left.Kind, right.Kind) switch
            {
                (Kind.Any, _) or (_, Kind.Any) => true,
                (Kind.Int32 or Kind.NativeInt, Kind.Int32 or Kind.NativeInt) => true,
                (Kind.Int64, Kind.Int64) or (Kind.Float, Kind.Float) => true,
                (Kind.Reference, Kind.Reference) => true,
                (Kind.Reference, Kind.NativeInt) or (Kind.NativeInt, Kind.Reference) => equality,
                (Kind.Object, Kind.Object) => equality,
                _ => false,
            };
            if (!valid) Fail($"操作数 {left} 与 {right} 不能比较");
        }

        private void Convert(Slot result, bool unsigned = false)
        {
            var value = Pop();
            var valid = value.Kind is Kind.Any or Kind.Int32 or Kind.Int64 or Kind.NativeInt
                || value.Kind == Kind.Float && !unsigned
                || value.Kind == Kind.Reference && result.Kind is Kind.NativeInt or Kind.Int64;
            if (!valid) Fail($"不能从 {value} 转换");
            Push(result);
        }

        private void Invoke(MethodReference callee, bool construct)
        {
            for (var i = callee.Parameters.Count - 1; i >= 0; i--)
                PopInto(Substitute(callee.Parameters[i].ParameterType, callee), $"{callee.Name} 的实参 {i} ");
            if (construct)
            {
                Push(Of(callee.DeclaringType));
                return;
            }
            if (callee.HasThis) PopOneOf($"{callee.Name} 的 this ", Kind.Object, Kind.Reference, Kind.NativeInt);
            if (Classify(Substitute(callee.ReturnType, callee)) is { } result) Push(result);
        }

        public (IReadOnlyList<Instruction> Targets, bool Falls) Step()
        {
            var operand = instruction.Operand;
            switch (instruction.OpCode.Code)
            {
                case Code.Nop or Code.Constrained or Code.Volatile or Code.Readonly or Code.Tail or Code.Unaligned: break;
                case Code.Ldarg_0: Push(Of(Argument(0))); break;
                case Code.Ldarg_1: Push(Of(Argument(1))); break;
                case Code.Ldarg_2: Push(Of(Argument(2))); break;
                case Code.Ldarg_3: Push(Of(Argument(3))); break;
                case Code.Ldarg or Code.Ldarg_S: Push(Of(Argument((ParameterDefinition)operand))); break;
                case Code.Ldarga or Code.Ldarga_S: Push(Ref); break;
                case Code.Starg or Code.Starg_S: PopInto(Argument((ParameterDefinition)operand), "参数"); break;
                case Code.Ldloc_0: Push(Of(body.Variables[0].VariableType)); break;
                case Code.Ldloc_1: Push(Of(body.Variables[1].VariableType)); break;
                case Code.Ldloc_2: Push(Of(body.Variables[2].VariableType)); break;
                case Code.Ldloc_3: Push(Of(body.Variables[3].VariableType)); break;
                case Code.Ldloc or Code.Ldloc_S: Push(Of(((VariableDefinition)operand).VariableType)); break;
                case Code.Ldloca or Code.Ldloca_S: Push(Ref); break;
                case Code.Stloc_0: PopInto(body.Variables[0].VariableType, "局部 "); break;
                case Code.Stloc_1: PopInto(body.Variables[1].VariableType, "局部 "); break;
                case Code.Stloc_2: PopInto(body.Variables[2].VariableType, "局部 "); break;
                case Code.Stloc_3: PopInto(body.Variables[3].VariableType, "局部 "); break;
                case Code.Stloc or Code.Stloc_S: PopInto(((VariableDefinition)operand).VariableType, "局部 "); break;
                case Code.Ldnull or Code.Ldstr: Push(O); break;
                case Code.Ldc_I4_M1 or Code.Ldc_I4_0 or Code.Ldc_I4_1 or Code.Ldc_I4_2 or Code.Ldc_I4_3 or Code.Ldc_I4_4
                    or Code.Ldc_I4_5 or Code.Ldc_I4_6 or Code.Ldc_I4_7 or Code.Ldc_I4_8 or Code.Ldc_I4_S or Code.Ldc_I4: Push(I4); break;
                case Code.Ldc_I8: Push(I8); break;
                case Code.Ldc_R4 or Code.Ldc_R8: Push(F); break;
                case Code.Dup: { var top = Pop(); Push(top); Push(top); break; }
                case Code.Pop: Pop(); break;
                case Code.Call or Code.Callvirt: Invoke((MethodReference)operand, false); break;
                case Code.Newobj: Invoke((MethodReference)operand, true); break;
                case Code.Ret:
                    if (Classify(method.ReturnType) is { } returned) Expect(Pop(), returned, "返回值");
                    if (stack.Count != 0) Fail($"返回时栈上仍有 {stack.Count} 个值");
                    return ([], false);
                case Code.Br or Code.Br_S: return ([(Instruction)operand], false);
                case Code.Leave or Code.Leave_S: stack.Clear(); return ([(Instruction)operand], false);
                case Code.Brfalse or Code.Brfalse_S or Code.Brtrue or Code.Brtrue_S:
                    PopOneOf("条件", Kind.Int32, Kind.Int64, Kind.NativeInt, Kind.Object, Kind.Reference);
                    return ([(Instruction)operand], true);
                case Code.Beq or Code.Beq_S or Code.Bne_Un or Code.Bne_Un_S:
                    Compare(true);
                    return ([(Instruction)operand], true);
                case Code.Bge or Code.Bge_S or Code.Bgt or Code.Bgt_S or Code.Ble or Code.Ble_S or Code.Blt or Code.Blt_S
                    or Code.Bge_Un or Code.Bge_Un_S or Code.Ble_Un or Code.Ble_Un_S or Code.Blt_Un or Code.Blt_Un_S:
                    Compare(false);
                    return ([(Instruction)operand], true);
                case Code.Bgt_Un or Code.Bgt_Un_S:
                    Compare(true);
                    return ([(Instruction)operand], true);
                case Code.Switch:
                    PopOneOf("switch 的值", Kind.Int32, Kind.NativeInt);
                    return ((Instruction[])operand, true);
                case Code.Ceq or Code.Cgt_Un: Compare(true); Push(I4); break;
                case Code.Cgt or Code.Clt or Code.Clt_Un: Compare(false); Push(I4); break;
                case Code.Add or Code.Sub: Numeric(false, true); break;
                case Code.Mul or Code.Div or Code.Rem: Numeric(false, false); break;
                case Code.Div_Un or Code.Rem_Un or Code.And or Code.Or or Code.Xor: Numeric(true, false); break;
                case Code.Shl or Code.Shr or Code.Shr_Un:
                    {
                        PopOneOf("移位量", Kind.Int32, Kind.NativeInt);
                        var value = Pop();
                        if (value.Kind is not (Kind.Int32 or Kind.Int64 or Kind.NativeInt or Kind.Any)) Fail($"不能移位 {value}");
                        Push(value);
                        break;
                    }
                case Code.Neg or Code.Not:
                    {
                        var value = Pop();
                        if (value.Kind is not (Kind.Int32 or Kind.Int64 or Kind.NativeInt or Kind.Any) && !(value.Kind == Kind.Float && instruction.OpCode.Code == Code.Neg))
                            Fail($"操作数不能是 {value}");
                        Push(value);
                        break;
                    }
                case Code.Ckfinite: PopOneOf("操作数", Kind.Float); Push(F); break;
                case Code.Conv_I1 or Code.Conv_I2 or Code.Conv_I4 or Code.Conv_U1 or Code.Conv_U2 or Code.Conv_U4
                    or Code.Conv_Ovf_I1 or Code.Conv_Ovf_I2 or Code.Conv_Ovf_I4 or Code.Conv_Ovf_U1 or Code.Conv_Ovf_U2 or Code.Conv_Ovf_U4
                    or Code.Conv_Ovf_I1_Un or Code.Conv_Ovf_I2_Un or Code.Conv_Ovf_I4_Un or Code.Conv_Ovf_U1_Un or Code.Conv_Ovf_U2_Un or Code.Conv_Ovf_U4_Un:
                    Convert(I4); break;
                case Code.Conv_I8 or Code.Conv_U8 or Code.Conv_Ovf_I8 or Code.Conv_Ovf_U8 or Code.Conv_Ovf_I8_Un or Code.Conv_Ovf_U8_Un: Convert(I8); break;
                case Code.Conv_I or Code.Conv_U or Code.Conv_Ovf_I or Code.Conv_Ovf_U or Code.Conv_Ovf_I_Un or Code.Conv_Ovf_U_Un: Convert(I); break;
                case Code.Conv_R4 or Code.Conv_R8: Convert(F); break;
                case Code.Conv_R_Un: Convert(F, unsigned: true); break;
                case Code.Ldind_I1 or Code.Ldind_U1 or Code.Ldind_I2 or Code.Ldind_U2 or Code.Ldind_I4 or Code.Ldind_U4:
                    PopOneOf("地址", Kind.Reference, Kind.NativeInt); Push(I4); break;
                case Code.Ldind_I8: PopOneOf("地址", Kind.Reference, Kind.NativeInt); Push(I8); break;
                case Code.Ldind_I: PopOneOf("地址", Kind.Reference, Kind.NativeInt); Push(I); break;
                case Code.Ldind_R4 or Code.Ldind_R8: PopOneOf("地址", Kind.Reference, Kind.NativeInt); Push(F); break;
                case Code.Ldind_Ref: PopOneOf("地址", Kind.Reference, Kind.NativeInt); Push(O); break;
                case Code.Stind_I1 or Code.Stind_I2 or Code.Stind_I4 or Code.Stind_I8 or Code.Stind_I or Code.Stind_R4 or Code.Stind_R8 or Code.Stind_Ref:
                    {
                        var expected = instruction.OpCode.Code switch
                        {
                            Code.Stind_I8 => I8,
                            Code.Stind_I => I,
                            Code.Stind_R4 or Code.Stind_R8 => F,
                            Code.Stind_Ref => O,
                            _ => I4,
                        };
                        Expect(Pop(), expected, "存入的值");
                        PopOneOf("地址", Kind.Reference, Kind.NativeInt);
                        break;
                    }
                case Code.Ldobj: PopOneOf("地址", Kind.Reference, Kind.NativeInt); Push(Of((TypeReference)operand)); break;
                case Code.Stobj: PopInto((TypeReference)operand, "存入的值"); PopOneOf("地址", Kind.Reference, Kind.NativeInt); break;
                case Code.Initobj: PopOneOf("地址", Kind.Reference, Kind.NativeInt); break;
                case Code.Ldfld:
                    {
                        var field = (FieldReference)operand;
                        PopOneOf("对象", Kind.Object, Kind.Reference, Kind.NativeInt, Kind.Value);
                        Push(Of(Substitute(field.FieldType, field)));
                        break;
                    }
                case Code.Ldflda: PopOneOf("对象", Kind.Object, Kind.Reference, Kind.NativeInt); Push(Ref); break;
                case Code.Stfld:
                    {
                        var field = (FieldReference)operand;
                        PopInto(Substitute(field.FieldType, field), $"字段 {field.Name} ");
                        PopOneOf("对象", Kind.Object, Kind.Reference, Kind.NativeInt);
                        break;
                    }
                case Code.Ldsfld: { var field = (FieldReference)operand; Push(Of(Substitute(field.FieldType, field))); break; }
                case Code.Ldsflda: Push(Ref); break;
                case Code.Stsfld: { var field = (FieldReference)operand; PopInto(Substitute(field.FieldType, field), $"静态字段 {field.Name} "); break; }
                case Code.Newarr: PopOneOf("数组长度", Kind.Int32, Kind.NativeInt); Push(O); break;
                case Code.Ldlen: PopOneOf("数组", Kind.Object); Push(I); break;
                case Code.Ldelema: PopOneOf("下标", Kind.Int32, Kind.NativeInt); PopOneOf("数组", Kind.Object); Push(Ref); break;
                case Code.Ldelem_Any: PopOneOf("下标", Kind.Int32, Kind.NativeInt); PopOneOf("数组", Kind.Object); Push(Of((TypeReference)operand)); break;
                case Code.Ldelem_I1 or Code.Ldelem_U1 or Code.Ldelem_I2 or Code.Ldelem_U2 or Code.Ldelem_I4 or Code.Ldelem_U4
                    or Code.Ldelem_I8 or Code.Ldelem_I or Code.Ldelem_R4 or Code.Ldelem_R8 or Code.Ldelem_Ref:
                    PopOneOf("下标", Kind.Int32, Kind.NativeInt);
                    PopOneOf("数组", Kind.Object);
                    Push(instruction.OpCode.Code switch
                    {
                        Code.Ldelem_I8 => I8,
                        Code.Ldelem_I => I,
                        Code.Ldelem_R4 or Code.Ldelem_R8 => F,
                        Code.Ldelem_Ref => O,
                        _ => I4,
                    });
                    break;
                case Code.Stelem_Any:
                    PopInto((TypeReference)operand, "元素");
                    PopOneOf("下标", Kind.Int32, Kind.NativeInt);
                    PopOneOf("数组", Kind.Object);
                    break;
                case Code.Stelem_I1 or Code.Stelem_I2 or Code.Stelem_I4 or Code.Stelem_I8 or Code.Stelem_I or Code.Stelem_R4 or Code.Stelem_R8 or Code.Stelem_Ref:
                    Expect(Pop(), instruction.OpCode.Code switch
                    {
                        Code.Stelem_I8 => I8,
                        Code.Stelem_I => I,
                        Code.Stelem_R4 or Code.Stelem_R8 => F,
                        Code.Stelem_Ref => O,
                        _ => I4,
                    }, "元素");
                    PopOneOf("下标", Kind.Int32, Kind.NativeInt);
                    PopOneOf("数组", Kind.Object);
                    break;
                case Code.Box: PopInto((TypeReference)operand, "装箱的值"); Push(O); break;
                case Code.Unbox: PopOneOf("对象", Kind.Object); Push(Ref); break;
                case Code.Unbox_Any: PopOneOf("对象", Kind.Object); Push(Of((TypeReference)operand)); break;
                case Code.Isinst or Code.Castclass: PopOneOf("对象", Kind.Object); Push(O); break;
                case Code.Ldtoken: Push(Any); break;
                case Code.Ldftn: Push(I); break;
                case Code.Ldvirtftn: PopOneOf("对象", Kind.Object); Push(I); break;
                case Code.Sizeof: Push(I4); break;
                case Code.Localloc: PopOneOf("大小", Kind.Int32, Kind.NativeInt); Push(I); break;
                case Code.Throw: PopOneOf("异常", Kind.Object); return ([], false);
                case Code.Rethrow: return ([], false);
                case Code.Endfinally: stack.Clear(); return ([], false);
                case Code.Endfilter: PopOneOf("过滤结果", Kind.Int32); return ([], false);
                default: Fail("未定义的指令"); return ([], false);
            }
            return ([], true);
        }
    }
}
