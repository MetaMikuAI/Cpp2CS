using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // RGCTX 引用的仍是当前开放参数；把已证明的引用共享 ABI 传给这些符号和运行时操作。
        private void BindSharedReferences()
        {
            TypeRef Type(TypeRef type) => type.Substitute(method.TypeArguments, method.MethodArguments);
            object? Bind(object? value) => value switch
            {
                TypeRef type => Type(type),
                MethodRef target => target with
                {
                    TypeArguments = target.TypeArguments.Select(Type).ToArray(),
                    MethodArguments = target.MethodArguments.Select(Type).ToArray(),
                },
                FieldRef field => field with { DeclaringType = Type(field.DeclaringType) },
                ValueTuple<object?, int> pair => (Bind(pair.Item1), pair.Item2),
                _ => value,
            };
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var statement = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e,
                        part => part is Symbol symbol ? symbol with { Value = Bind(symbol.Value)! } : null));
                    if (statement is Call { Op: { } op } call) statement = call with { Op = op with { Operand = Bind(op.Operand) } };
                    block.Statements[i] = statement;
                }
        }
    }
}
