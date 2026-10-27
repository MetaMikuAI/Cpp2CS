using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>托管调用的 ABI 返回片；聚合片由结构体贡献者定型，不能把整个结构类型赋给每个机器寄存器。其余定义是破坏值。</summary>
internal sealed class CallResultContributor : ITypeContributor
{
    public string Name => "调用结果";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var abi = new ManagedAbi(context.Types.Layouts);
        foreach (var call in context.Statements.OfType<Call>())
        {
            if (call.Op is not (null or { Kind: OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallDelegate or OpKind.CallGenericVirtual or OpKind.CallMethodPointer })
                || context.Resolve(call) is not { } method || abi.Classify(method, out _) is not { } signature) continue;
            var returned = signature.Return;
            if (returned is not null && context.Types.Kind(returned.Type) != TypeKind.Struct)
                foreach (var piece in returned.Pieces)
                {
                    var index = Array.IndexOf(call.Results, piece.Register);
                    if (index >= 0 && index < call.Defines.Length && call.Defines[index] is { } variable)
                        constraints.Defines(variable, returned.Type, new(Name, call.Address, $"{method} 返回 {piece.Register}:{piece.Width} : {returned.Type}"));
                }
            // 不是返回片的定义都是被调用者破坏的寄存器（AAPCS64 的调用者保存寄存器），没有值。
            var pieces = returned?.Pieces.Select(p => p.Register).ToHashSet() ?? [];
            for (var i = 0; i < call.Defines.Length && i < call.Results.Length; i++)
                if (call.Defines[i] is { } clobbered && !pieces.Contains(call.Results[i]))
                    constraints.IsClobbered(clobbered, new(Name, call.Address, $"{method} 破坏 {call.Results[i]}"));
        }
    }
}
