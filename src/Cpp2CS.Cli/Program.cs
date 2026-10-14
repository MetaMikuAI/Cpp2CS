using System.Diagnostics;
using Cpp2CS.Functions;
using Cpp2CS.Images;

namespace Cpp2CS.Cli;

/// <summary>
/// 命令行入口。目前的命令只用于验证底层证据层：
///   inspect &lt;binary&gt; [--ranges &lt;n&gt;]   一次构建函数边界表并报告统计与覆盖缺口
/// </summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        Console.OutputEncoding = System.Text.Encoding.UTF8;
        if (args.Length < 2 || args[0] != "inspect")
        {
            Console.Error.WriteLine("用法: cpp2cs inspect <binary> [--ranges <n>] [--skipped <n>]");
            return 2;
        }
        var rangesToShow = Argument(args, "--ranges") ?? 0;
        var skippedToShow = Argument(args, "--skipped") ?? 20;

        var watch = Stopwatch.StartNew();
        var image = ImageDocument.Load(args[1]);
        Console.WriteLine($"文件      {args[1]}");
        Console.WriteLine($"架构      {image.Architecture}  基址 0x{image.PreferredBase:x}  映像 0x{image.PreferredBase:x}..0x{image.PreferredBase + image.Ranges.Max(r => r.Address + r.MemorySize - image.PreferredBase):x}");
        Console.WriteLine($"SHA256    {image.Sha256}");
        Console.WriteLine($"映射段    {image.Ranges.Count}（可执行 {image.ExecutableRanges.Count}）");
        Console.WriteLine($"重定位表  {image.RelocationTables.Count}，落进代码段 {image.CodeRelocations.Count}");
        Console.WriteLine($"导出函数  {image.Exports.Count}");
        Console.WriteLine($"加载耗时  {watch.ElapsedMilliseconds} ms");

        watch.Restart();
        var table = FunctionTable.Build(image);
        Console.WriteLine();
        Console.WriteLine($"边界来源  {table.Source}");
        Console.WriteLine($"函数数量  {table.Ranges.Count}");
        Console.WriteLine($"解析耗时  {watch.ElapsedMilliseconds} ms");
        if (table.Ranges.Count > 0)
        {
            var sizes = table.Ranges.Select(r => (long)r.Size).Order().ToArray();
            Console.WriteLine($"范围      最小 {sizes[0]}  中位 {sizes[sizes.Length / 2]}  最大 {sizes[^1]}  合计 {sizes.Sum()}");
            var withLsda = table.Ranges.Count(r => r.ExceptionRegions.Length > 0);
            Console.WriteLine($"含 LSDA   {withLsda} 个函数，异常区间 {table.Ranges.Sum(r => r.ExceptionRegions.Length)} 条");
            var withFragments = table.Ranges.Count(r => r.Fragments.Length > 0);
            Console.WriteLine($"链式片段  {withFragments} 个函数，片段 {table.Ranges.Sum(r => r.Fragments.Length)} 段");
            foreach (var group in table.Ranges.Where(r => r.Handler is not null).GroupBy(r => r.Handler!.Value).OrderByDescending(g => g.Count()))
                Console.WriteLine($"处理例程  0x{group.Key:x}  {group.Count()} 个函数");
        }
        Console.WriteLine($"跳过条目  {table.Skipped.Count}");
        foreach (var reason in table.Skipped.Take((int)skippedToShow)) Console.WriteLine($"          {reason}");

        if (rangesToShow > 0)
        {
            Console.WriteLine();
            foreach (var range in table.Ranges.Take((int)rangesToShow))
                Console.WriteLine($"          {range.Describe()}  异常区间 {range.ExceptionRegions.Length}");
        }
        return 0;
    }

    private static long? Argument(string[] args, string name)
    {
        var index = Array.IndexOf(args, name);
        if (index < 0) return null;
        if (index + 1 >= args.Length) throw new ArgumentException($"{name} 缺少取值");
        return long.Parse(args[index + 1]);
    }
}
