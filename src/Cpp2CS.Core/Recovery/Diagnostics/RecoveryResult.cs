using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Analysis;

/// <summary>可预期的恢复阻塞；不用于内部不变量错误。</summary>
internal sealed record RecoveryFailure(ulong Address, string Message, bool Derived = false, RecoveryHole? Cause = null,
    Variable? Unresolved = null, string Code = "recovery.unsupported");

internal readonly record struct RecoveryUnit;

/// <summary>成功值和失败原因分开传播，失败不得作为托管值进入 IR。</summary>
internal readonly struct RecoveryResult<T>
{
    private readonly T? value;
    private readonly bool initialized;
    public RecoveryFailure? Failure { get; }
    private RecoveryResult(T value) { this.value = value; initialized = true; }
    private RecoveryResult(RecoveryFailure failure) { Failure = failure; initialized = true; }
    public bool TryGet(out T result, out RecoveryFailure failure)
    {
        if (!initialized) throw new InvalidOperationException("恢复结果尚未初始化");
        result = value!;
        failure = Failure!;
        return Failure is null;
    }
    public RecoveryResult<U> Map<U>(Func<T, U> map) => TryGet(out var result, out var failure) ? map(result) : failure;
    public RecoveryResult<U> Bind<U>(Func<T, RecoveryResult<U>> bind) => TryGet(out var result, out var failure) ? bind(result) : failure;
    public static implicit operator RecoveryResult<T>(T value) => new(value);
    public static implicit operator RecoveryResult<T>(RecoveryFailure failure) => new(failure);
}
