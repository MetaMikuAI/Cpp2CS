using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Targets.Elf;
namespace Cpp2CS.Tests;

internal static class InputSampleChecks
{
    public const string Command = "input-sample";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_SAMPLES");
        if (string.IsNullOrEmpty(root)) { Console.WriteLine("跳过 Input 样本检查：未设置 CPP2CS_SAMPLES。"); return 0; }
        // 进程的峰值内存是累计的：同一进程里先跑过别的大检查时，它不再反映这一项的用量。
        var baseline = Process.GetCurrentProcess().PeakWorkingSet64;
        using var manifest = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(root, "manifest.json")));
        // 清单中的首个 ELF64/v31 组是主样本；目录身份来自外部清单。
        var group = manifest.RootElement.GetProperty("groups").EnumerateObject().First(g =>
            g.Value.GetProperty("files").EnumerateArray().Any(f => f.TryGetProperty("binary", out var b) && b.GetProperty("format").GetString() == "ELF") &&
            g.Value.GetProperty("files").EnumerateArray().Any(f => f.TryGetProperty("metadata", out var m) && m.GetProperty("version_int32").GetInt32() == 31));
        var files = group.Value.GetProperty("files").EnumerateArray().ToArray();
        string Local(JsonElement file) => Path.Combine(root, group.Name, file.GetProperty("copy").GetString()!.Replace('\\', '/').Split('/')[^1]);
        var binary = files.Single(f => f.TryGetProperty("binary", out _));
        var metadata = files.Single(f => f.TryGetProperty("metadata", out _));
        var timer = Stopwatch.StartNew();
        var image = ElfImage.Load(Local(binary));
        var imageSeconds = timer.Elapsed.TotalSeconds;
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model, builder) = ModelBuilder.Load(image, Local(metadata), spec);
        var modelSeconds = timer.Elapsed.TotalSeconds - imageSeconds;
        var (registrations, problems) = RegistrationReader.Read(image, model, spec, builder.CodeRegistration, builder.MetadataRegistration);
        var entries = registrations.Entries.Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod).Select(e => e.Method!.Method).Distinct().Count();
        var peak = Process.GetCurrentProcess().PeakWorkingSet64;
        Console.WriteLine($"主样本：类型 {model.Types.Count}，方法 {model.Methods.Count}，有入口的方法 {entries}，泛型实例 {model.MethodSpecs.Count}，注册元数据槽 {registrations.MetadataUsageSlots.Count}");
        Console.WriteLine($"主样本：映像 {imageSeconds:F2}s，模型 {modelSeconds:F2}s，注册表 {timer.Elapsed.TotalSeconds - imageSeconds - modelSeconds:F2}s，总计 {timer.Elapsed.TotalSeconds:F2}s，峰值工作集 {peak / 1024d / 1024:F1} MiB");
        var a = new Assertions();
        a.True(problems.Count == 0, "样本注册表没有未解释的错误");
        a.True(timer.Elapsed.TotalSeconds < 120, "样本两分钟内");
        if (baseline <= 512L * 1024 * 1024) a.True(peak <= 2.5 * 1024 * 1024 * 1024, "样本峰值内存不超过 2.5 GiB");
        else Console.WriteLine("峰值内存的断言只在单独运行本命令时生效：进程里已有其他检查的占用。");
        return a.Finish("Input 样本检查");
    }
}
