namespace Cpp2CS.Tests;

/// <summary>测试入口：每个命令对应一类基于真实二进制或参照实现的检查。</summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        return args.FirstOrDefault() switch
        {
            "arm64-oracle" => Arm64Oracle.Run(args.Skip(1).Where(a => !a.StartsWith("--")).ToArray(), 4),
            "model" when args.Length >= 3 => ModelCheck.Run(args[1], args[2], args.ElementAtOrDefault(3)),
            "cfg" when args.Length >= 3 => CfgCheck.Run(args[1], args[2], args.ElementAtOrDefault(3)),
            _ => Usage(),
        };
    }

    private static int Usage()
    {
        Console.Error.WriteLine("""
            用法: Cpp2CS.Tests arm64-oracle <oracle.jsonl>...
                  Cpp2CS.Tests model <binary> <metadata> [script.json]
                  Cpp2CS.Tests cfg <binary> <metadata> [0x地址 | 命名空间,...]
            """);
        return 2;
    }
}
