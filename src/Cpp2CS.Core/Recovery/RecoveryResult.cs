namespace Cpp2CS.Recovery;

/// <summary>可预期的恢复阻塞：地址、原因与产生它的步骤；不用于内部不变量错误。</summary>
public sealed record RecoveryFailure(ulong Address, string Reason, string Rule);

/// <summary>成功值和失败原因分开传播，失败不得作为托管值进入 IR。</summary>
public readonly struct RecoveryResult<T>
{
    private readonly T? value;
    public RecoveryFailure? Failure { get; }
    private RecoveryResult(T value) => this.value = value;
    private RecoveryResult(RecoveryFailure failure) => Failure = failure;

    public bool TryGet(out T result, out RecoveryFailure failure)
    {
        result = value!;
        failure = Failure!;
        return Failure is null;
    }

    public RecoveryResult<U> Map<U>(Func<T, U> map) => TryGet(out var result, out var failure) ? map(result) : failure;
    public RecoveryResult<U> Bind<U>(Func<T, RecoveryResult<U>> bind) => TryGet(out var result, out var failure) ? bind(result) : failure;
    public static implicit operator RecoveryResult<T>(T value) => new(value);
    public static implicit operator RecoveryResult<T>(RecoveryFailure failure) => new(failure);
}

internal static class RecoveryDiagnostics
{
    internal static RecoveryFailure Fail(ulong address, string reason, string rule) => new(address, reason, rule);
}
