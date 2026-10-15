namespace Cpp2CS.Tests;

/// <summary>测试入口：每个命令对应一类基于真实二进制或参照实现的检查。</summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        return args.FirstOrDefault() switch
        {
            "managed-calls" => ManagedCallsCheck.Run(),
            "managed-returns" => ManagedReturnsCheck.Run(),
            "value-layouts" => ValueLayoutsCheck.Run(),
            "layout-model" when args.Length >= 3 => LayoutModelCheck.Run(args[1], args[2]),
            "values" when args.Length >= 4 => ValuesRun.Run(args[1], args[2], args[3], args.ElementAtOrDefault(4)),
            "value-check" when args.Length >= 3 => ValueRecoveryCheck.Run(args[1], args[2]),
            "body-check" when args.Length >= 3 => BodyEmissionCheck.Run(args[1], args[2]),
            "accessor-check" when args.Length >= 3 => AccessorCheck.Run(args[1], args[2]),
            "phi-check" when args.Length >= 3 => PhiRecoveryCheck.Run(args[1], args[2]),
            "edge-check" when args.Length == 1 || args.Length >= 3 => EdgeConstantsCheck.Run(args.ElementAtOrDefault(1), args.ElementAtOrDefault(2)),
            "stack-check" when args.Length >= 3 => StackRecoveryCheck.Run(args[1], args[2]),
            "aggregate-check" when args.Length >= 3 => AggregateRecoveryCheck.Run(args[1], args[2]),
            "buffer-check" when args.Length >= 3 => BufferRecoveryCheck.Run(args[1], args[2]),
            "runtime-check" when args.Length >= 3 => RuntimeValueCheck.Run(args[1], args[2]),
            "constructor-check" when args.Length >= 3 => ConstructorCheck.Run(args[1], args[2]),
            "class-init-check" when args.Length >= 3 => ClassInitializationCheck.Run(args[1], args[2]),
            "static-field-check" when args.Length >= 3 => StaticFieldCheck.Run(args[1], args[2]),
            "boxing-check" when args.Length >= 3 => BoxingCheck.Run(args[1], args[2]),
            "boxing-source-check" when args.Length >= 2 => BoxingCheck.Saved(args[1]),
            "bodies" when args.Length >= 4 => BodiesRun.Run(args[1], args[2], args[3], args.ElementAtOrDefault(4)),
            "arm64-oracle" => Arm64Oracle.Run(args.Skip(1).Where(a => !a.StartsWith("--")).ToArray(), 4),
            "model" when args.Length >= 3 => ModelCheck.Run(args[1], args[2], args.ElementAtOrDefault(3)),
            "cfg" when args.Length >= 3 => CfgCheck.Run(args[1], args[2], args.ElementAtOrDefault(3)),
            "ssa" when args.Length >= 3 => SsaRun.Run(args[1], args[2], args.ElementAtOrDefault(3)),
            "prep" when args.Length >= 3 => PrepRun.Run(args[1], args[2], args.ElementAtOrDefault(3)),
            "copyfind" when args.Length >= 4 => HelperCensus.Find(args[1], args[2], Convert.ToUInt64(args[3], 16)),
            "copydiff" when args.Length >= 5 => HelperCensus.Diff(args[1], args[2], Convert.ToUInt64(args[3], 16), Convert.ToUInt64(args[4], 16)),
            "skeleton" when args.Length >= 4 => SkeletonCheck.Run(args[1], args[2], args[3], args.ElementAtOrDefault(4)),
            "compile" when args.Length >= 4 => CompileCheck.Run(args[1], args[2], args[3], args.ElementAtOrDefault(4)),
            "compile-saved" when args.Length >= 2 => CompileCheck.Saved(args[1], args.ElementAtOrDefault(2), args.ElementAtOrDefault(3) ?? "Assembly-CSharp"),
            "helpers" when args.Length >= 3 => HelperCensus.Run(args[1], args[2], args.ElementAtOrDefault(3)),
            _ => Usage(),
        };
    }

    private static int Usage()
    {
        Console.Error.WriteLine("""
            用法: Cpp2CS.Tests arm64-oracle <oracle.jsonl>...
                  Cpp2CS.Tests managed-calls
                  Cpp2CS.Tests managed-returns
                  Cpp2CS.Tests value-layouts
                  Cpp2CS.Tests layout-model <binary> <metadata>
                  Cpp2CS.Tests values <binary> <metadata> <报告.jsonl> [命名空间,...]
                  Cpp2CS.Tests value-check <binary> <metadata>
                  Cpp2CS.Tests body-check <binary> <metadata>
                  Cpp2CS.Tests accessor-check <binary> <metadata>
                  Cpp2CS.Tests phi-check <binary> <metadata>
                  Cpp2CS.Tests edge-check [binary metadata]
                  Cpp2CS.Tests stack-check <binary> <metadata>
                  Cpp2CS.Tests aggregate-check <binary> <metadata>
                  Cpp2CS.Tests buffer-check <binary> <metadata>
                  Cpp2CS.Tests runtime-check <binary> <metadata>
                  Cpp2CS.Tests constructor-check <binary> <metadata>
                  Cpp2CS.Tests class-init-check <binary> <metadata>
                  Cpp2CS.Tests static-field-check <binary> <metadata>
                  Cpp2CS.Tests boxing-check <binary> <metadata>
                  Cpp2CS.Tests boxing-source-check <已保存的 BoxingChecks.dll>
                  Cpp2CS.Tests bodies <binary> <metadata> <输出目录> [命名空间,...]
                  Cpp2CS.Tests model <binary> <metadata> [script.json]
                  Cpp2CS.Tests cfg <binary> <metadata> [0x地址 | 命名空间,...]
                  Cpp2CS.Tests ssa <binary> <metadata> [0x地址 | 命名空间,...]
                  Cpp2CS.Tests prep <binary> <metadata> [0x地址 | 命名空间,...]
                  Cpp2CS.Tests helpers <binary> <metadata> [命名空间,...]
                  Cpp2CS.Tests skeleton <binary> <metadata> <输出目录> [类型全名,...]
                  Cpp2CS.Tests compile <binary> <metadata> <输出目录> [回归命名空间,...]
                  Cpp2CS.Tests compile-saved <程序集目录> [回归命名空间,...] [程序集名]
            """);
        return 2;
    }
}
