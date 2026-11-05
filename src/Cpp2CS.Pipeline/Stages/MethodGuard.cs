using Cpp2CS.Recovery;

namespace Cpp2CS.Pipeline;

/// <summary>
/// --keep-going 的逐方法保护：在独立线程上恢复一个方法，崩溃或超时变成带原因的洞。
/// .NET 不能中止线程，超时的线程留在后台继续运行，它用的恢复器不再使用；恢复器的缓存也可能停在中间状态，所以崩溃后同样换新的。
/// 栈溢出不能捕获，这里给足够大的栈，真的溢出时进程仍然会退出。
/// </summary>
internal sealed class MethodGuard(Func<MethodDecompiler> create, TimeSpan limit, Action<string> log)
{
    private const int StackBytes = 64 * 1024 * 1024;
    private int crashes, timeouts;

    public int Crashes => crashes;
    public int Timeouts => timeouts;

    /// <summary>worker 在失败后换成新的。</summary>
    public MethodRecoveryResult Run(MethodRef method, ulong entry, ref MethodDecompiler worker, Func<MethodDecompiler, MethodRecoveryResult> recover)
    {
        MethodRecoveryResult? result = null;
        Exception? failure = null;
        var current = worker;
        var thread = new Thread(() =>
        {
            try { result = recover(current); }
            // 这里是这个选项唯一的用途：记录失败并继续，原因写进洞。
            catch (Exception e) { failure = e; }
        }, StackBytes) { IsBackground = true };
        thread.Start();
        string reason;
        if (!thread.Join(limit))
        {
            Interlocked.Increment(ref timeouts);
            reason = $"恢复 超过时限 {limit.TotalSeconds:F0} s";
        }
        else if (failure is not null)
        {
            Interlocked.Increment(ref crashes);
            var at = failure.StackTrace?.Split('\n').FirstOrDefault()?.Trim();
            reason = $"恢复 崩溃 {failure.GetType().Name}：{failure.Message}（{at}）";
        }
        else return result!;
        log($"0x{entry:x} {method}：{reason}");
        worker = create();
        return new MethodRecoveryResult(method, entry, null, [new RecoveryHole(entry, reason)]);
    }
}
