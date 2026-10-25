namespace Cpp2CS.Tests;

/// <summary>测试入口：可执行断言程序，每个命令一类检查，命令由 <see cref="CommandAttribute"/> 声明。失败时返回 1。</summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        return Commands.Dispatch(args);
    }
}

internal sealed class Assertions
{
    private int failures;
    private int passes;

    public void True(bool condition, string message)
    {
        if (condition) { passes++; return; }
        failures++;
        Console.WriteLine($"✗ {message}");
    }

    public void Equal<T>(T expected, T actual, string message) =>
        True(EqualityComparer<T>.Default.Equals(expected, actual), $"{message}：期望 {expected}，实际 {actual}");

    public int Finish(string name)
    {
        Console.WriteLine(failures == 0 ? $"✓ {name}：{passes} 项通过" : $"✗ {name}：{failures} 项失败，{passes} 项通过");
        return failures == 0 ? 0 : 1;
    }
}
