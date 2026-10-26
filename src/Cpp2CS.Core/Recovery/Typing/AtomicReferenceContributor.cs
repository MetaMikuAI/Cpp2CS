using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

internal sealed class AtomicReferenceContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "原子引用";

    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var expressions = input.Expressions(context);
        foreach (var call in context.Statements.OfType<Call>())
            if (call is { Op.Kind: OpKind.CompareExchangeReference, Arguments: [var address, _, _] }
                && call.Defines.FirstOrDefault() is { } result && expressions.LocationType(address, 64) is { } type
                && context.Types.Kind(type) == TypeKind.Reference)
                constraints.Defines(result, type, new(Name, call.Address, "旧值类型来自原子交换的存储位置"));
    }
}
