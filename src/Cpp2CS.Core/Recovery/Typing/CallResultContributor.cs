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
            if (call is { Kind: CallKind.Direct, Op: { Kind: OpKind.Import, Operand: string symbol }, Results: [var output], Defines: [{ } imported] }
                && output == Storage.Vec(0) && MathImportSignature.Find(symbol) is { } math && call.Arguments.Length == math.Parameters.Length)
                constraints.Defines(imported, math.Single ? context.Types.Single : context.Types.Double, new(Name, call.Address, $"数学导入 {symbol} 返回值"));
            if (call is { Op: { Kind: OpKind.ImportOutPair, Operand: "sincosf" }, Defines: [{ } sine, { } cosine] })
            {
                constraints.Defines(sine, context.Types.Single, new(Name, call.Address, "sincosf sine 出参"));
                constraints.Defines(cosine, context.Types.Single, new(Name, call.Address, "sincosf cosine 出参"));
            }
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
