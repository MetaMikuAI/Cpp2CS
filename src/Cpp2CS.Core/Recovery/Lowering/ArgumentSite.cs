using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>实参规则看到的调用现场：<c>Argument</c> 取单个寄存器传递的实参（不是时登记洞）。</summary>
internal sealed record ArgumentSite(Call Call, MethodRef Callee, string Name, Dictionary<Storage, Expr> Registers, Func<AbiValue, string, RecoveryResult<Expr>> Argument)
{
    public int Index { get; init; }
    public required List<ManagedStatement> Output { get; init; }
}
