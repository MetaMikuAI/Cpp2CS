using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>F4 的具体分配类型；Invoke 的泛型代入由 Resolve 与 ABI 返回片规则处理，不扩大 T1 的实参范围。</summary>
internal sealed class DelegateContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "委托";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        foreach (var (call, type) in input.DelegateCreations)
            if (input.Constructed.TryGetValue(call, out var variable))
                constraints.Defines(variable, type, new(Name, call.Address, "已证明唯一构造与时序的具体委托类型"));
    }
}
