using Cpp2CS.Pipeline;

namespace Cpp2CS.Cli;

internal static class RecoverCommand
{
    public static int Run(string[] args)
    {
        if (args is ["runtime-shapes", var referenceImage, var referenceSymbols, var destination])
        {
            RuntimeShapeGeneration.Generate(referenceImage, referenceSymbols, destination);
            return 0;
        }
        if (args is not ["recover", var image, var metadata, var output, .. var options])
        {
            Console.Error.WriteLine("用法: recover <映像> <元数据> <输出目录> [--method 名称子串或方法身份] [--assembly 程序集文件名] [--address 0x偏移] [--jobs 并行度] [--symbols 未去符号的映像] [--unity 版本] [--source]\n      runtime-shapes <参考映像> <同次构建符号映像> <规格输出 JSON>");
            return 2;
        }
        var request = new RecoveryRequest(image, metadata, output)
        { Progress = (processed, total) => Console.Error.WriteLine($"已处理方法 {processed}/{total}") };
        for (var i = 0; i < options.Length; i += 2)
        {
            if (options[i] == "--source") { request = request with { Source = true }; i--; continue; }
            if (i + 1 == options.Length) throw new ArgumentException($"{options[i]} 缺少值");
            var value = options[i + 1];
            request = options[i] switch
            {
                "--method" => request with { Method = value },
                "--assembly" => request with { Assembly = value },
                "--address" => request with { Address = value.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? Convert.ToUInt64(value[2..], 16) : ulong.Parse(value) },
                "--jobs" => request with { Jobs = int.Parse(value) },
                "--unity" => request with { UnityVersion = value },
                "--symbols" => request with { Symbols = value },
                _ => throw new ArgumentException($"未知参数 {options[i]}")
            };
        }
        var report = new RecoverySession().Run(request);
        Console.WriteLine($"方法 {report.Summary.Methods}，完整 {report.Summary.Complete}，洞 {report.Summary.Holes}，无方法体 {report.Summary.NoBody}，{report.Summary.ElapsedSeconds:F2}s，峰值 {report.Summary.PeakWorkingSetBytes / 1048576.0:F1} MiB");
        if (report.Summary.ContractFailures.Length == 0 && report.Summary.ProgramErrors.Length == 0) return 0;
        foreach (var failure in report.Summary.ContractFailures) Console.Error.WriteLine(failure);
        Console.Error.WriteLine($"程序错误 {report.Summary.ProgramErrors.Length} 个，契约失败 {report.Summary.ContractFailures.Length} 个；详见 recovery.json 的 summary。");
        return 3;
    }
}
