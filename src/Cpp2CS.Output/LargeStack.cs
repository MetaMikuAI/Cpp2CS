using System.Runtime.ExceptionServices;

namespace Cpp2CS.Output;

/// <summary>
/// 按嵌套深度递归的工作（校验、写出、反编译）放到大栈的专用线程上。
/// 默认的线程栈装不下几百层的表达式，而栈溢出不能接住，会结束整个进程。
/// </summary>
public static class LargeStack
{
    /// <summary>栈按需提交，保留的只是地址空间。</summary>
    public const int Bytes = 256 * 1024 * 1024;

    public static void Run(Action work) => ForEach(1, 1, _ => work());

    /// <summary>逐个分发 0..count-1；工作里抛出的第一个异常原样带回调用线程。</summary>
    public static void ForEach(int count, int workers, Action<int> body)
    {
        int next = -1;
        ExceptionDispatchInfo? error = null;
        void Work()
        {
            try
            {
                for (int i; Volatile.Read(ref error) is null && (i = Interlocked.Increment(ref next)) < count;) body(i);
            }
            // 只把异常带回调用线程，不改变它的含义。
            catch (Exception e) { Interlocked.CompareExchange(ref error, ExceptionDispatchInfo.Capture(e), null); }
        }
        var threads = Enumerable.Range(0, Math.Max(0, Math.Min(workers, count))).Select(_ => new Thread(Work, Bytes)).ToArray();
        foreach (var thread in threads) thread.Start();
        foreach (var thread in threads) thread.Join();
        error?.Throw();
    }
}
