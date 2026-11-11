using System.Reflection;

namespace Cpp2CS.Tests;

internal static class Program
{
    // 检查按约定发现：带 Command 常量和无参 Run 方法的静态类。新增检查不改这里。
    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        const BindingFlags flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static;
        var checks = (
            from type in typeof(Program).Assembly.GetTypes()
            let field = type.GetField("Command", flags)
            let run = type.GetMethod("Run", flags, Type.EmptyTypes)
            where field is { IsLiteral: true } && field.FieldType == typeof(string) && run?.ReturnType == typeof(int)
            let command = (string)field.GetRawConstantValue()!
            orderby command
            select (Command: command, Run: run!)).ToArray();
        var unknown = args.Except(checks.Select(check => check.Command)).ToArray();
        if (unknown.Length != 0)
        {
            Console.Error.WriteLine($"未知的检查：{string.Join(' ', unknown)}");
            Console.Error.WriteLine($"用法: Cpp2CS.Tests [{string.Join('|', checks.Select(check => check.Command))}]；不带参数运行全部检查。");
            return 2;
        }
        var result = 0;
        foreach (var check in checks.Where(check => args.Length == 0 || args.Contains(check.Command)))
            result |= (int)check.Run.Invoke(null, null)!;
        return result;
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
