namespace Cpp2CS.Tests;

internal static class Program
{
    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        if (args is []) return ArchitectureChecks.Run() | ModelChecks.Run() | ManagedChecks.Run() | RuntimeSpecChecks.Run();
        if (args is ["arch"]) return ArchitectureChecks.Run();
        if (args is ["model"]) return ModelChecks.Run();
        if (args is ["managed"]) return ManagedChecks.Run();
        if (args is ["runtime"]) return RuntimeSpecChecks.Run();
        Console.Error.WriteLine("用法: Cpp2CS.Tests [arch|model|managed|runtime]；不带参数运行全部检查。");
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
        Console.Error.WriteLine($"✗ {message}");
    }

    public int Finish(string name)
    {
        Console.WriteLine($"{name}：{passes} 项通过，{failures} 项失败");
        return failures == 0 ? 0 : 1;
    }
}
