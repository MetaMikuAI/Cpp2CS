using System.Collections.Immutable;

namespace Cpp2CS.Nir;

public sealed record NirExceptionType : NirType
{
    public static readonly NirExceptionType Instance = new();
}
public sealed record NirExceptionCreate(NirValue Result, NirEffectFlow Flow) : NirOperation;
public sealed record NirRaise(NirValue Exception, NirValue Effect) : NirTerminator;

// 调用结果仅由后继块参数定义；Captured 不含结果或 Effect。
public sealed record NirInvokeEdge(NirBlockId Target, ImmutableArray<NirValue> Captured);
public sealed record NirInvoke(NirCallTarget Target, ImmutableArray<NirValue> Arguments,
    NirInvokeEdge? Normal, NirInvokeEdge Unwind, NirValue Effect) : NirTerminator;

// 身份由执行上下文分配，不包含对象地址、语言类型或机器展开状态。
public sealed class NirExceptionToken
{
    public long Id { get; }
    internal NirExecutionContext Owner { get; }
    internal NirExceptionToken(long id, NirExecutionContext owner) => (Id, Owner) = (id, owner);
}
