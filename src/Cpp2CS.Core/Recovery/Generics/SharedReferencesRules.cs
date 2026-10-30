using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class SharedReferencesRules
{
    internal static void BindSharedReferences(this RecoveryScope ctx)
    {
        TypeRef Type(TypeRef type) => type.Substitute(ctx.method.TypeArguments, ctx.method.MethodArguments);
        object? Bind(object? value) => value switch
        {
            TypeRef type => Type(type),
            MethodRef target => target with
            {
                TypeArguments = target.TypeArguments.Select(Type).ToArray(),
                MethodArguments = target.MethodArguments.Select(Type).ToArray(),
            },
            FieldRef field => field with
            {
                DeclaringType = Type(field.DeclaringType)
            },
            ValueTuple<TypeRef, MethodRef> constrained => (Type(constrained.Item1), (MethodRef)Bind(constrained.Item2)!),
            ValueTuple<object?, int> pair => (Bind(pair.Item1), pair.Item2),
            _ => value,
        };
        foreach (var block in ctx.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, part => part is Symbol symbol ? symbol with { Value = Bind(symbol.Value)! } : null));
                if (statement is Call { Op: { } op } call)
                    statement = call with
                    {
                        Op = op with
                        {
                            Operand = Bind(op.Operand)
                        }
                    };
                ctx.Rewriter.Replace(block, i, statement);
            }
    }
}
