using System.Runtime.CompilerServices;

namespace Cpp2CS.Native;

/// <summary>管线判定有方法不结束时置位。公共设施在入口处调用 <see cref="Check"/>，使不结束的方法带着调用栈以程序错误收场；不参与任何判定。</summary>
public static class WorkAbort
{
    private static volatile bool requested;
    public static bool Requested => requested;
    public static void Request() => requested = true;
    public static void Reset() => requested = false;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Check() { if (requested) Throw(); }
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Throw() => throw new TimeoutException("方法恢复超过时限，已中止");
}
