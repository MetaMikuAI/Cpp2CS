using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>旧 InferTypes 的 phiUses 反传：来源在该 φ 处被当作目标类型使用。</summary>
internal sealed class PhiUseContributor : ITypeContributor
{
    public string Name => "汇合使用";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        foreach (var phi in context.Statements.OfType<Phi>())
            if (context.TypeOf(phi.Target) is { } type)
                foreach (var source in phi.Sources)
                    constraints.Requires(source, type, new(Name, phi.Address, $"{source} 在 φ {phi.Target} 中使用"));
    }
}
