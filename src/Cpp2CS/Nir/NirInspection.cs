using System.Collections.Immutable;

namespace Cpp2CS.Nir;

public static class NirInspection
{
    public static ImmutableArray<NirValue> Results(NirOperation operation) => operation switch
    {
        NirConstant x => [x.Result], NirPure x => [x.Result], NirFunctionConstant x => [x.Result],
        NirFloat x => [x.Result, x.Exceptions],
        NirExceptionCreate x => [x.Result, x.Flow.Output],
        NirAtomicRmw x => [x.Result, x.Flow.Output], NirCompareExchange x => [x.OldValue, x.Success, x.Flow.Output],
        NirFence x => [x.Flow.Output],
        NirLoad x => [x.Result, x.Flow.Output], NirStore x => [x.Flow.Output],
        NirLocalAlloc x => [x.Result, x.Flow.Output], NirCall x => [.. x.Results, x.Flow.Output],
        NirChoose x => [x.Result, x.Flow.Output],
        NirEnvironmentRead x => [x.Result, x.Flow.Output], NirEnvironmentWrite x => [x.Flow.Output],
        _ => throw new ArgumentOutOfRangeException(nameof(operation))
    };
    public static ImmutableArray<NirValue> Inputs(NirOperation operation) => operation switch
    {
        NirConstant or NirFunctionConstant => [], NirPure x => x.Inputs,
        NirExceptionCreate x => [x.Flow.Input],
        NirFloat x => [.. x.Inputs, .. x.Controls?.Values ?? []],
        NirAtomicRmw x => [x.Address, x.Value, x.Flow.Input],
        NirCompareExchange x => [x.Address, x.Expected, x.Replacement, x.Flow.Input], NirFence x => [x.Flow.Input],
        NirLoad x => [x.Address, x.Flow.Input], NirStore x => [x.Address, x.Value, x.Flow.Input],
        NirLocalAlloc x => [x.Size, x.Flow.Input],
        NirCall x => [.. TargetInputs(x.Target), .. x.Arguments, x.Flow.Input],
        NirChoose x => [x.Flow.Input],
        NirEnvironmentRead x => [x.Flow.Input], NirEnvironmentWrite x => [x.Value, x.Flow.Input],
        _ => throw new ArgumentOutOfRangeException(nameof(operation))
    };
    public static NirEffectFlow? Flow(NirOperation operation) => operation switch
    {
        NirLoad x => x.Flow, NirStore x => x.Flow, NirLocalAlloc x => x.Flow,
        NirAtomicRmw x => x.Flow, NirCompareExchange x => x.Flow, NirFence x => x.Flow,
        NirExceptionCreate x => x.Flow,
        NirCall x => x.Flow, NirChoose x => x.Flow,
        NirEnvironmentRead x => x.Flow, NirEnvironmentWrite x => x.Flow, _ => null
    };
    public static ImmutableArray<NirEdge> Edges(NirTerminator terminator) => terminator switch
    {
        NirJump x => [x.Edge], NirBranch x => [x.WhenTrue, x.WhenFalse], _ => []
    };
    public static ImmutableArray<NirBlockId> Successors(NirTerminator terminator) => terminator switch
    {
        NirInvoke x => x.Normal is { } normal ? [normal.Target, x.Unwind.Target] : [x.Unwind.Target],
        _ => [.. Edges(terminator).Select(edge => edge.Target)]
    };
    public static ImmutableArray<NirValue> Inputs(NirTerminator terminator) => terminator switch
    {
        NirJump x => x.Edge.Arguments,
        NirBranch x => [x.Condition, .. x.WhenTrue.Arguments, .. x.WhenFalse.Arguments],
        NirReturn x => [.. x.Values, x.Effect],
        NirTailCall x => [.. TargetInputs(x.Target), .. x.Arguments, x.Effect],
        NirNoReturnCall x => [.. TargetInputs(x.Target), .. x.Arguments, x.Effect],
        NirRaise x => [x.Exception, x.Effect],
        NirInvoke x => [.. TargetInputs(x.Target), .. x.Arguments, .. x.Normal?.Captured ?? [], .. x.Unwind.Captured, x.Effect],
        NirFault x => [x.Effect], NirTerminate x => [x.Effect],
        _ => throw new ArgumentOutOfRangeException(nameof(terminator))
    };
    public static ImmutableArray<NirValue> TargetInputs(NirCallTarget target) => target is NirIndirectTarget x ? [x.Function] : [];
    public static bool TypeEquals(NirType left, NirType right) => (left, right) switch
    {
        (NirBitsType a, NirBitsType b) => a.Width == b.Width,
        (NirEffectType, NirEffectType) => true,
        (NirExceptionType, NirExceptionType) => true,
        (NirAddressType a, NirAddressType b) => a.Space == b.Space && a.Width == b.Width,
        (NirFunctionType a, NirFunctionType b) => a.Outcomes == b.Outcomes && SignatureEquals(a.Signature, b.Signature),
        _ => false
    };
    public static bool SignatureEquals(NirSignature a, NirSignature b) => TypesEqual(a.Parameters, b.Parameters) && TypesEqual(a.Results, b.Results);
    public static bool TypesEqual(IEnumerable<NirType> a, IEnumerable<NirType> b) => a.SequenceEqual(b, NirTypeComparer.Instance);
    private sealed class NirTypeComparer : IEqualityComparer<NirType>
    {
        public static readonly NirTypeComparer Instance = new();
        public bool Equals(NirType? x, NirType? y) => x is not null && y is not null && TypeEquals(x, y);
        public int GetHashCode(NirType obj) => 0;
    }
}
