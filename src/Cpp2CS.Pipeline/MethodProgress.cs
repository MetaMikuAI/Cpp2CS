using System.Diagnostics;

namespace Cpp2CS.Pipeline;

/// <summary>当前线程正在恢复的方法走到了哪一步。只供慢方法诊断读取，不参与判定。</summary>
public sealed class MethodProgress
{
    [ThreadStatic] private static MethodProgress? current;
    private volatile string step = "开始";
    public long Started { get; } = Stopwatch.GetTimestamp();
    public string Step => step;
    public static void Begin(MethodProgress? progress) => current = progress;
    public static void Mark(string name) { if (current is { } progress) progress.step = name; }
}
