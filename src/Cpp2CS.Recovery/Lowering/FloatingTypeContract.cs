using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>下降出口的浮点类型核对；类型要求不由写出器补足。</summary>
public static class FloatingTypeContract
{
    public static Reason? Check(ManagedBody body, ManagedTypes types)
    {
        bool Float(TypeRef type) => types.Kind(type) is TypeKind.Float or TypeKind.Double;
        Reason? Use(ManagedValue value, TypeRef expected, string use) => (Float(expected) || Float(value.Type))
            && (!Equals(value.Type, expected) || value.Width != types.StorageBits(expected))
                ? new("lowering.Float.Type", use + " 需要 " + expected + "，实际为 " + value.Type + "/" + value.Width) : null;
        Reason? Arguments(MethodRef method, IReadOnlyList<ManagedValue> values)
        {
            if (values.Count != method.Method.Parameters.Count)
                return new("lowering.Float.Type", "调用实参数量与签名不符：" + method);
            for (int i = 0; i < values.Count; i++)
            {
                var expected = method.Concrete(method.Method.Parameters[i].Type);
                if (!Float(expected) && !Float(values[i].Type)) continue;
                if (Use(values[i], expected, method + " 的实参 " + i) is { } why) return why;
            }
            return null;
        }
        var locals = new Dictionary<LocalId, LocalValue>();
        Reason? Source(ManagedValue value)
        {
            if (value is LocalValue local)
            {
                if (locals.TryGetValue(local.Id, out var declaration))
                {
                    if ((Float(local.Type) || Float(declaration.Type)) && (!Equals(local.Type, declaration.Type) || local.Width != declaration.Width))
                        return new("lowering.Float.Type", "同一局部身份具有不同的浮点与整数声明");
                }
                else locals.Add(local.Id, local);
            }
            TypeRef? declared = value switch
            {
                ArgumentValue argument when argument.Index >= 0 && argument.Index < body.Method.Method.Parameters.Count
                    => body.Method.Concrete(body.Method.Method.Parameters[argument.Index].Type),
                ArgumentValue { Index: -1 } when !body.Method.Method.IsStatic => body.Method.Method.Owner.IsValueType
                    ? new ByRefRef(body.Method.DeclaringType) : body.Method.DeclaringType,
                FieldValue field => field.Field.Field.Type.Substitute((field.Field.DeclaringType as DefinitionRef)?.Arguments ?? [], []),
                StaticFieldValue field => field.Field.Field.Type.Substitute((field.Field.DeclaringType as DefinitionRef)?.Arguments ?? [], []),
                StaticCallValue call => call.Method.Concrete(call.Method.Method.ReturnType),
                IndirectValue { Address.Type: ByRefRef address } => address.Element,
                _ => null,
            };
            if (declared is not null) return Use(value, declared, "值的声明来源");
            return value is ArgumentValue && Float(value.Type) ? new("lowering.Float.Type", "浮点形参值没有对应的形参声明") : null;
        }
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            var statementProblem = statement switch
            {
                ManagedCall call => Arguments(call.Invocation.Method, call.Invocation.Arguments)
                    ?? (call.Result is { } result ? Use(result, call.Invocation.Method.Concrete(call.Invocation.Method.Method.ReturnType), "调用结果局部") : null),
                ManagedReturn { Value: { } value } => Use(value, body.Method.Concrete(body.Method.Method.ReturnType), "返回值"),
                ManagedStore store => Use(store.Value, store.Target.Type, "写入值"),
                ManagedAssignment assignment => Use(assignment.Value, assignment.Target.Type, "局部赋值"),
                _ => null,
            };
            if (statementProblem is not null) return statementProblem;
            foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies))
                if (Use(copy.Value, copy.Target.Type, "合流输入") is { } why) return why;
            IEnumerable<ManagedValue> targets = statement switch
            {
                ManagedAssignment assignment => [assignment.Target], ManagedCall { Result: { } result } => [result], _ => [],
            };
            foreach (var target in targets.Concat(ManagedValues.Edges(statement).SelectMany(e => e.Copies).Select(c => c.Target)))
                if (Source(target) is { } targetSource) return targetSource;
            foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk))
            {
                if (Source(value) is { } valueSource) return valueSource;
                if (Float(value.Type) && value.Width != types.StorageBits(value.Type))
                    return new("lowering.Float.Type", "浮点值的位宽与声明类型不符");
                var problem = value switch
                {
                    ChoiceValue choice => Use(choice.True, choice.Type, "选择真臂") ?? Use(choice.False, choice.Type, "选择假臂"),
                    NewObjectValue created => Arguments(created.Constructor, created.Arguments),
                    BoxValue boxed => Use(boxed.Operand, boxed.Boxed, "装箱值"),
                    UnaryValue unary when Float(unary.Type) => Use(unary.Operand, unary.Type, "浮点一元操作数"),
                    ComparisonValue comparison when Float(comparison.Left.Type) || Float(comparison.Right.Type)
                        => Use(comparison.Right, comparison.Left.Type, "浮点比较操作数"),
                    ComposedValue composed => composed.Leaves.Select(l => Use(l.Value, l.Path.Last().Field.Type.Substitute((l.Path.Last().DeclaringType as DefinitionRef)?.Arguments ?? [], []), "结构体叶子")).FirstOrDefault(p => p is not null),
                    BinaryValue binary when Float(binary.Type) => Use(binary.Left, binary.Type, "浮点左操作数") ?? Use(binary.Right, binary.Type, "浮点右操作数"),
                    ConversionValue { Kind: ConversionKind.FloatToFloat or ConversionKind.FloatToSignedInteger or ConversionKind.FloatToUnsignedInteger } conversion
                        when !Float(conversion.Operand.Type) => new Reason("lowering.Float.Type", "浮点转换的输入不是浮点值"),
                    ConversionValue { Kind: ConversionKind.ZeroExtend or ConversionKind.SignExtend or ConversionKind.Truncate } conversion
                        when Float(conversion.Type) || Float(conversion.Operand.Type) => new Reason("lowering.Float.Type", "整数扩展或截断的输入输出含浮点类型"),
                    ConversionValue { Kind: ConversionKind.Bitcast } conversion when (Float(conversion.Type) || Float(conversion.Operand.Type))
                        && (conversion.Width != conversion.Operand.Width || Float(conversion.Type) && conversion.Width != types.StorageBits(conversion.Type))
                        => new Reason("lowering.Float.Type", "浮点位重解释的输入输出位宽不相同"),
                    _ => null,
                };
                if (problem is not null) return problem;
            }
        }
        return null;
    }
}
