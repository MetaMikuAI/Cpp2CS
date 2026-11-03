namespace Cpp2CS.Tests;

/// <summary>测试入口。execute：原生机器码与写出的 CIL 在同一合成内存上的执行对照。</summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        return args switch
        {
            ["check-models", var binary, var metadata, var cache] => ArchitectureChecks.Run(binary, metadata, cache),
            ["execute", var binary, var metadata, var list, .. var options] => Execution.ExecutionCheck.Run(binary, metadata, list, options),
            _ => Usage(),
        };
    }

    private static int Usage()
    {
        Console.Error.WriteLine("用法: Cpp2CS.Tests execute <libil2cpp.so> <global-metadata.dat> <方法清单> [--fact-cache-file 文件] [--cases N] [--output 结果.tsv] [--verbose]");
        Console.Error.WriteLine("      Cpp2CS.Tests check-models <libil2cpp.so> <global-metadata.dat> <事实缓存>");
        return 2;
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
