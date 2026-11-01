namespace Cpp2CS.Diagnostics;

/// <summary>
/// 门禁运行中常开的计数器。只计数，不影响恢复结果；进程内累计，由运行清单（run.json 的 counters）写出。
/// </summary>
public static class GateCounters
{
    private static long valueEqualKeys;

    /// <summary>以值相等为键的语句表中，结构相同而对象不同的键被判为相等的次数。为 0 时这些表可以改为引用相等而不改变结果。</summary>
    public static long ValueEqualKeys => Interlocked.Read(ref valueEqualKeys);

    internal static void CountValueEqualKey() => Interlocked.Increment(ref valueEqualKeys);
}
