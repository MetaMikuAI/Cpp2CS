using System.Reflection;

namespace Cpp2CS.Tests;

/// <summary>门禁中怎样运行一个检查：不带参数、带映像（binary、metadata），或带映像和本检查的输出目录。</summary>
internal enum Gate { None, Unit, Image, ImageOutput }

/// <summary>
/// 声明一个测试命令。标在静态方法上；参数全部是 string，按位置绑定命令行，最后一个 string[] 参数接收其余参数。
/// 新增检查只需在自己的文件里加这个属性，命令表、用法说明与门禁清单（<c>gate-list</c>）都由它生成。
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class CommandAttribute(string name, string description) : Attribute
{
    public string Name => name;
    public string Description => description;
    /// <summary>参数说明，例如 <c>&lt;binary&gt; &lt;metadata&gt; &lt;输出目录&gt;</c>。</summary>
    public string Arguments { get; init; } = "";
    public Gate Gate { get; init; }
}

internal static class Commands
{
    private sealed record Command(CommandAttribute Info, MethodInfo Method, int Required, bool Rest);

    private static readonly Command[] All = Discover();

    public static int Dispatch(string[] args)
    {
        if (args is ["unit-tests"])
        {
            var failed = 0;
            foreach (var command in All.Where(c => c.Info.Gate == Gate.Unit))
                if (Invoke(command, []) != 0) failed++;
            Console.WriteLine($"通用检查：{All.Count(c => c.Info.Gate == Gate.Unit)} 项，失败 {failed} 项");
            return failed == 0 ? 0 : 1;
        }
        if (args is ["gate-list"])
        {
            foreach (var command in All.Where(c => c.Info.Gate != Gate.None)) Console.WriteLine(command.Info.Name);
            return 0;
        }
        if (args is ["gate", var name, var lib, var output])
        {
            if (All.FirstOrDefault(c => c.Info.Name == name && c.Info.Gate != Gate.None) is not { } gated) return Usage();
            string[] image = [Path.Combine(lib, "libil2cpp.so"), Path.Combine(lib, "global-metadata.dat")];
            return Invoke(gated, gated.Info.Gate switch
            {
                Gate.Unit => [],
                Gate.Image => image,
                _ => [.. image, Path.Combine(output, name)],
            });
        }
        if (args.Length > 0 && All.FirstOrDefault(c => c.Info.Name == args[0]) is { } found
            && (args.Length - 1 == found.Required || found.Rest && args.Length - 1 >= found.Required))
            return Invoke(found, args[1..]);
        return Usage();
    }

    private static int Invoke(Command command, string[] arguments)
    {
        object?[] values = command.Rest
            ? [.. arguments[..command.Required], arguments[command.Required..]]
            : [.. arguments];
        try { return (int)command.Method.Invoke(null, values)!; }
        catch (TargetInvocationException e) when (e.InnerException is not null)
        {
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e.InnerException).Throw();
            throw;
        }
    }

    private static Command[] Discover()
    {
        var commands = typeof(Commands).Assembly.GetTypes()
            .SelectMany(t => t.GetMethods(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
            .Select(m => (Method: m, Info: m.GetCustomAttribute<CommandAttribute>()))
            .Where(p => p.Info is not null)
            .Select(p =>
            {
                var parameters = p.Method.GetParameters();
                var rest = parameters.Length > 0 && parameters[^1].ParameterType == typeof(string[]);
                var required = rest ? parameters.Length - 1 : parameters.Length;
                if (p.Method.ReturnType != typeof(int) || parameters.Take(required).Any(q => q.ParameterType != typeof(string)))
                    throw new InvalidOperationException($"命令 {p.Info!.Name}：{p.Method.DeclaringType}.{p.Method.Name} 必须返回 int，参数只能是 string 加可选的末尾 string[]");
                return new Command(p.Info!, p.Method, required, rest);
            })
            .OrderBy(c => c.Info.Name, StringComparer.Ordinal).ToArray();
        if (commands.GroupBy(c => c.Info.Name).FirstOrDefault(g => g.Count() > 1) is { } duplicate)
            throw new InvalidOperationException($"命令 {duplicate.Key} 声明了多次");
        if (commands.FirstOrDefault(c => c.Info.Gate switch
            {
                Gate.Unit => c.Required != 0,
                Gate.Image => c.Required != 2,
                Gate.ImageOutput => c.Required != 3,
                _ => false,
            }) is { } mismatched)
            throw new InvalidOperationException($"命令 {mismatched.Info.Name} 的门禁方式 {mismatched.Info.Gate} 与参数个数 {mismatched.Required} 不符");
        return commands;
    }

    internal static int Usage()
    {
        Console.Error.WriteLine("用法: Cpp2CS.Tests <命令> [参数]");
        Console.Error.WriteLine("      Cpp2CS.Tests unit-tests                      运行不依赖目标映像的检查");
        Console.Error.WriteLine("      Cpp2CS.Tests gate-list                       列出声明了运行方式的检查");
        Console.Error.WriteLine("      Cpp2CS.Tests gate <命令> <lib 目录> <输出目录>  以门禁的标准参数运行一个检查");
        foreach (var command in All)
        {
            var head = $"      Cpp2CS.Tests {command.Info.Name} {command.Info.Arguments}".TrimEnd();
            Console.Error.WriteLine(head.Length < 60 ? $"{head.PadRight(60)}{command.Info.Description}" : $"{head}\n{new string(' ', 60)}{command.Info.Description}");
        }
        return 2;
    }
}
