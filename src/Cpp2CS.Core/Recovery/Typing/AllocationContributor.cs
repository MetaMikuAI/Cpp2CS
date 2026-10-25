using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Typing;

internal sealed class AllocationContributor : ITypeContributor
{
    public string Name => "分配";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        foreach (var call in context.Statements.OfType<Call>())
        {
            TypeRef? type = call.Op switch
            {
                { Kind: OpKind.NewObject, Operand: TypeRef t } => t,
                { Kind: OpKind.NewArray, Operand: ArrayRef t } => t,
                { Kind: OpKind.Box } => context.Types.Object,
                { Kind: OpKind.IsInst, Operand: TypeRef t } => t,
                _ => null,
            };
            if (type is not null)
                foreach (var variable in call.Defines.OfType<Variable>())
                    constraints.Defines(variable, type, new(Name, call.Address, $"{call.Op!.Kind} : {type}"));
        }
    }
}
