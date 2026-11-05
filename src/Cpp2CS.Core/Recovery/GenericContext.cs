using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery;

/// <summary>
/// 方法的泛型上下文。共享泛型代码经自身 MethodInfo 与 RGCTX 得到的元数据实体以定义的类型参数表达；
/// L2 之后按当前实例（封闭实例，或带原生绑定的开放形式）代入一次，之后各层直接使用实体，不再各自代入。
/// 封闭实体代入后不变；写出定义时实例即定义本身，代入是恒等。
/// </summary>
internal static class GenericContext
{
    public static void Instantiate(MachineFunction function, MethodRef method)
    {
        if (method.TypeArguments.Count + method.MethodArguments.Count == 0) return;
        Expr? Symbol(Expr e) => e switch
        {
            Symbol s when Instantiate(s.Value, method) is var value && !ReferenceEquals(value, s.Value) => s with { Value = value! },
            ClassProperty p when Instantiate(p.Type, method) is TypeRef type && !ReferenceEquals(type, p.Type) => p with { Type = type },
            StackAllocation a when Instantiate(a.Element, method) is TypeRef element && !ReferenceEquals(element, a.Element) => a with { Element = element },
            _ => null,
        };
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                // 泛型参数的相等不比较原生绑定：实参只差绑定时 MapOperands 按值比较会保留原语句，调用直接重建。
                Expr Bound(Expr e) => ExprMap.Map(e, Symbol);
                var statement = block.Statements[i] is Call original
                    ? original with
                    {
                        Target = Bound(original.Target),
                        Arguments = original.Arguments.Select(Bound).ToArray(),
                        DelegateReceiver = original.DelegateReceiver is { } receiver ? Bound(receiver) : null,
                        StackPointer = original.StackPointer is { } pointer ? Bound(pointer) : null,
                    }
                    : ExprMap.MapOperands(block.Statements[i], Bound);
                if (statement is Call { Op: { } op } call && Instantiate(op.Operand, method) is var operand && !ReferenceEquals(operand, op.Operand))
                    statement = call with { Op = op with { Operand = operand } };
                block.Statements[i] = statement;
            }
    }

    /// <summary>元数据实体在当前实例中的形式；不含类型参数的值原样返回。</summary>
    public static object? Instantiate(object? value, MethodRef method) => value switch
    {
        TypeRef type => Same(type, method.Concrete(type)),
        MethodRef callee => Instantiate(callee, method),
        FieldRef field => Same(field.DeclaringType, method.Concrete(field.DeclaringType)) is var owner && !ReferenceEquals(owner, field.DeclaringType)
            ? field with { DeclaringType = owner } : field,
        ValueTuple<object?, int> pair => Instantiate(pair.Item1, method) is var first && !ReferenceEquals(first, pair.Item1) ? (first, pair.Item2) : pair,
        ValueTuple<TypeRef, MethodRef> constrained => ((TypeRef)Instantiate(constrained.Item1, method)!, Instantiate(constrained.Item2, method)) is var mapped
            && (!ReferenceEquals(mapped.Item1, constrained.Item1) || !ReferenceEquals(mapped.Item2, constrained.Item2)) ? mapped : constrained,
        _ => value,
    };

    private static MethodRef Instantiate(MethodRef callee, MethodRef method)
    {
        var types = callee.TypeArguments.Select(t => Same(t, method.Concrete(t))).ToArray();
        var methods = callee.MethodArguments.Select(t => Same(t, method.Concrete(t))).ToArray();
        return types.SequenceEqual(callee.TypeArguments, ReferenceEqualityComparer.Instance) && methods.SequenceEqual(callee.MethodArguments, ReferenceEqualityComparer.Instance)
            ? callee : callee with { TypeArguments = types, MethodArguments = methods };
    }

    /// <summary>结构相同则保留原对象，使未变化的语句不被重建。</summary>
    private static TypeRef Same(TypeRef original, TypeRef substituted) => original.Equals(substituted) && SameBinding(original, substituted) ? original : substituted;

    /// <summary>泛型参数的相等不比较原生绑定；代入带来绑定时须视为变化。</summary>
    private static bool SameBinding(TypeRef a, TypeRef b) => (a, b) switch
    {
        (GenericParameterRef x, GenericParameterRef y) => Equals(x.Binding, y.Binding),
        (DefinitionRef x, DefinitionRef y) => x.Arguments.Zip(y.Arguments).All(p => SameBinding(p.First, p.Second)),
        (ArrayRef x, ArrayRef y) => SameBinding(x.Element, y.Element),
        (PointerRef x, PointerRef y) => SameBinding(x.Element, y.Element),
        (ByRefRef x, ByRefRef y) => SameBinding(x.Element, y.Element),
        _ => true,
    };
}
