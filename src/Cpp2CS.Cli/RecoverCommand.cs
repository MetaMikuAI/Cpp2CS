using Cpp2CS.Pipeline;

namespace Cpp2CS.Cli;

internal static class RecoverCommand
{
    public static int Run(string[] args)
    {
        if (args is not ["recover", var image, var metadata, var output, .. var options])
        {
            Console.Error.WriteLine("用法: recover <映像> <元数据> <输出目录> [--method 名称子串] [--address 0x偏移] [--jobs 并行度] [--symbols 未去符号的映像] [--unity 版本] [--source]");
            return 2;
        }
        var request = new RecoveryRequest(image, metadata, output);
        for (var i = 0; i < options.Length; i += 2)
        {
            if (options[i] == "--source") { request = request with { Source = true }; i--; continue; }
            if (i + 1 == options.Length) throw new ArgumentException($"{options[i]} 缺少值");
            var value = options[i + 1];
            request = options[i] switch
            {
                "--method" => request with { Method = value },
                "--address" => request with { Address = value.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? Convert.ToUInt64(value[2..], 16) : ulong.Parse(value) },
                "--jobs" => request with { Jobs = int.Parse(value) },
                "--unity" => request with { UnityVersion = value },
                "--symbols" => request with { Symbols = value },
                _ => throw new ArgumentException($"未知参数 {options[i]}")
            };
        }
        var report = new RecoverySession().Run(request);
        Console.WriteLine($"方法 {report.Summary.Methods}，完整 {report.Summary.Complete}，洞 {report.Summary.Holes}，无方法体 {report.Summary.NoBody}，{report.Summary.ElapsedSeconds:F2}s，峰值 {report.Summary.PeakWorkingSetBytes / 1048576.0:F1} MiB");
        return 0;
    }
}
