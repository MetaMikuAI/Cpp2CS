using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>T2 配对不产生新类型；把已证成构造配对的分配类型列为独立证据，绝不由构造签名猜分配类型。</summary>
internal sealed class PairingContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "配对";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var allocations = context.Statements.OfType<Call>().Where(c => c.Op?.Kind == OpKind.NewObject)
            .SelectMany(c => c.Defines.OfType<Variable>().Select(v => (v, c))).ToDictionary(x => x.v, x => x.c);
        foreach (var (constructor, variable) in input.Constructed)
            if (allocations.TryGetValue(variable, out var allocation) && allocation.Op?.Operand is TypeRef type)
                constraints.Defines(variable, type, new(Name, constructor.Address, $"配对分配 0x{allocation.Address:x} → 构造；类型来自分配 {type}"));
    }
}
