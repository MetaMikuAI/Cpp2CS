using System.Reflection;
using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.Closure;

public static class FieldAccessors
{
    public static FieldAccessor? Recognize(ManagedBody original, bool write, ManagedTypes types)
    {
        var method = original.Method;
        var definition = method.Method;
        // 泛型类型的封闭实例（List<T>.Enumerator.get_Current 等）与值类型的实例访问器也可以认出；执行对照另行核对实例的原生代码。
        var generic = method.TypeArguments.Count > 0;
        if (definition.GenericParameters.Count > 0
            || definition.Owner.GenericParameters.Count != method.TypeArguments.Count || definition.Parameters.Count != (write ? 1 : 0)
            || (!definition.IsStatic && definition.IsVirtual && (definition.Attributes & MethodAttributes.Final) == 0)) return null;
        var returnType = definition.ReturnType.Substitute(method.TypeArguments, []);
        var parameterType = write ? definition.Parameters[0].Type.Substitute(method.TypeArguments, []) : null;
        // 与写出器使用同一组已有等价归一；不自行证明算术、分支或布尔归一的等价性。
        var body = ReadabilityRewriter.Rewrite(original, types, ReadabilityRewriter.FromEnvironment());
        var locals = new Dictionary<Variable, ManagedValue>();
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var seen = new HashSet<ulong>();
        var current = body.Blocks[0];
        var reads = 0;
        ManagedValue? storage = null;
        ManagedValue? Resolve(ManagedValue value) => value switch
        {
            LocalValue l => locals.GetValueOrDefault(l.Variable),
            ArgumentValue => value,
            FieldValue f when !definition.IsStatic && Resolve(f.Receiver) is ArgumentValue { Index: -1 } receiver => f with { Receiver = receiver },
            StaticFieldValue f when definition.IsStatic => f,
            ConversionValue c when c.Type.Equals(c.Operand.Type) && c.Width == c.Operand.Width => Resolve(c.Operand),
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } c when types.Kind(c.Type) == TypeKind.Int
                && Resolve(c.Operand) is { } inner && types.Kind(inner.Type) == TypeKind.Int => c with { Operand = inner },
            // ARM64 的 W 寄存器读取先扩成 X，再在返回处截回；穿过局部复制后仍是同一个字段的原位宽。
            ConversionValue { Kind: ConvKind.Truncate } c when types.Kind(c.Type) == TypeKind.Int
                && Resolve(c.Operand) is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } extended
                && extended.Operand.Width == c.Width && types.Kind(extended.Operand.Type) == TypeKind.Int => extended.Operand,
            _ => null,
        };
        bool Exact(ManagedValue value, TypeRef type) => FieldOf(value) is { } field && value.Type.Equals(type) && value.Width == types.Bits(type)
            && field.Field.IsStatic == definition.IsStatic
            && field.Field.Type.Substitute((field.DeclaringType as DefinitionRef)?.Arguments ?? [], []).Equals(type)
            // 静态调用和静态访存须触发同一个类型的初始化，不能凭单字段形态引入另一类型的 cctor。
            && (!definition.IsStatic || field.DeclaringType.Equals(method.DeclaringType));
        int Reads(ManagedValue value) => ManagedValues.Walk(value).Count(v => v is FieldValue or StaticFieldValue);
        FieldAccessor Result(ManagedValue value) => new(method, FieldOf(value)!, value.Type, value.Width, write);
        while (seen.Add(current.Address))
        {
            ManagedJump? next = null;
            for (var i = 0; i < current.Statements.Count; i++)
            {
                switch (current.Statements[i])
                {
                    case ManagedAssignment a:
                        reads += Reads(a.Value);
                        if (Resolve(a.Value) is not { } value || !a.Target.Type.Equals(value.Type) || a.Target.Width != value.Width) return null;
                        locals[a.Target.Variable] = value;
                        break;
                    case ManagedStore s when write && storage is null && Resolve(s.Target) is { } target
                        && Resolve(s.Value) is ArgumentValue { Index: 0 } parameter && parameter.Type.Equals(parameterType)
                        && parameter.Width == types.Bits(parameter.Type) && Exact(target, parameter.Type):
                        storage = target;
                        break;
                    case ManagedReturn r when i == current.Statements.Count - 1:
                        if (seen.Count != body.Blocks.Count) return null;
                        if (write) return r.Value is null && ManagedTypes.IsVoid(definition.ReturnType) && reads == 0 && storage is not null ? Result(storage) : null;
                        reads += r.Value is null ? 0 : Reads(r.Value);
                        return r.Value is not null && Resolve(r.Value) is { } returned && reads == 1 && Exact(returned, returnType) ? Result(returned) : null;
                    case ManagedJump j when i == current.Statements.Count - 1:
                        var copies = j.Edge.Copies.Select(c => (c.Target, Value: Resolve(c.Value))).ToArray();
                        if (copies.Any(c => c.Value is null || !c.Target.Type.Equals(c.Value.Type) || c.Target.Width != c.Value.Width)) return null;
                        reads += j.Edge.Copies.Sum(c => Reads(c.Value));
                        foreach (var c in copies) locals[c.Target.Variable] = c.Value!;
                        next = j;
                        break;
                    default: return null;
                }
            }
            if (next is null || !blocks.TryGetValue(next.Edge.Target, out current!)) return null;
        }
        return null;
    }


    public static bool Matches(this FieldAccessor accessor, ManagedTypes types, TypeDef caller, ManagedValue value, bool write) => accessor.Write == write
        && accessor.Field.Equals(FieldAccessor.FieldOf(value)) && accessor.ValueType.Equals(value.Type) && accessor.Width == value.Width
        && (value is StaticFieldValue ? accessor.Method.Method.IsStatic : value is FieldValue f && !accessor.Method.Method.IsStatic && (types.IsAssignable(f.Receiver.Type, accessor.Method.DeclaringType)
            || accessor.Method.Method.Owner.IsValueType && f.Receiver.Type is ByRefRef { Element: var element } && element.Equals(accessor.Method.DeclaringType)))
        && ManagedAccess.Method(types, caller, accessor.Method, FieldAccessor.ReceiverType(value));
    private static FieldRef? FieldOf(ManagedValue value) => FieldAccessor.FieldOf(value);
}
