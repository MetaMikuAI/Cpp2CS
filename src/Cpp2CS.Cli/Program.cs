using System.Diagnostics;
using System.Globalization;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Native;

if (args is ["--import", var inputBinary, var inputMetadata, var outputDirectory])
    return RawImport.Run(inputBinary, inputMetadata, outputDirectory);

if (args is ["--help"] or ["-h"] || args.Length == 0)
{
    Console.WriteLine("用法：Cpp2CS <binary> <metadata> <VA> [--diagnostics <目录>]");
    Console.WriteLine("默认输出 C#；退出码：0 完成，2 输入/导入失败，3 存在未恢复语义。");
    return 0;
}
if (args.Length != 3 && !(args.Length == 5 && args[3] == "--diagnostics"))
    return Error("用法：Cpp2CS <binary> <metadata> <VA> [--diagnostics <目录>]");
var addressText = args[2].StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? args[2][2..] : args[2];
if (!ulong.TryParse(addressText, NumberStyles.AllowHexSpecifier, CultureInfo.InvariantCulture, out var address))
    return Error("地址必须是十六进制 VA。");
if (!File.Exists(args[0])) return Error("二进制文件不存在。");
if (!File.Exists(args[1])) return Error("metadata 文件不存在。");
var binary = Path.GetFullPath(args[0]);
var metadata = Path.GetFullPath(args[1]);
using (var stream = File.OpenRead(binary))
{
    var header = new byte[64];
    if (stream.Read(header) != header.Length || !header.AsSpan(0, 6).SequenceEqual(new byte[] { 127, 69, 76, 70, 2, 1 })
        || header[18] != 183 || header[19] != 0)
        return Error("当前只支持 AArch64 ELF64 小端磁盘二进制。");
}
using (var stream = File.OpenRead(metadata))
{
    var header = new byte[8];
    if (stream.Read(header) != header.Length || !header.AsSpan(0, 4).SequenceEqual(new byte[] { 0xaf, 0x1b, 0xb1, 0xfa }))
        return Error("metadata 缺少有效的 IL2CPP 文件头。");
}
var capstone = Environment.GetEnvironmentVariable("CPP2CS_CAPSTONE") ?? "capstone";
if (!NativeLibrary.TryLoad(capstone, out var nativeHandle))
    return Error("无法加载 Capstone 5；请将其原生库加入系统库搜索路径，或设置 CPP2CS_CAPSTONE。");
NativeLibrary.Free(nativeHandle);
var binaryHash = Hash(binary);
var metadataHash = Hash(metadata);
var cache = Path.Combine(".cpp2cs", "cache", RawImport.Version, binaryHash + "-" + metadataHash);
var manifest = Path.Combine(cache, "assemblies.json");
if (!File.Exists(manifest))
{
    // 每次导入使用独立目录，失败或并发调用不会污染已有缓存。
    var pending = cache + ".pending-" + Guid.NewGuid().ToString("N");
    Directory.CreateDirectory(pending);
    var start = new ProcessStartInfo("dotnet") { UseShellExecute = false, CreateNoWindow = true, RedirectStandardOutput = true, RedirectStandardError = true };
    foreach (var argument in new[] { Assembly.GetExecutingAssembly().Location, "--import", binary, metadata, Path.GetFullPath(pending) })
        start.ArgumentList.Add(argument);
    using var process = Process.Start(start)!;
    var stdout = process.StandardOutput.ReadToEndAsync();
    var stderr = process.StandardError.ReadToEndAsync();
    process.WaitForExit();
    File.WriteAllText(Path.Combine(pending, "import.log"), stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult());
    if (process.ExitCode != 0 || !File.Exists(Path.Combine(pending, "assemblies.json")))
        return Error($"原始输入导入失败，详见 {pending}/import.log。");
    File.WriteAllText(Path.Combine(pending, "inputs.json"), JsonSerializer.Serialize(new { binarySha256 = binaryHash, metadataSha256 = metadataHash, importer = RawImport.Version }));
    // 并发导入通过目录移动发布缓存。
    try { Directory.Move(pending, cache); }
    catch (IOException) when (File.Exists(manifest)) { /* 接受并发进程发布的同一缓存。 */ }
}
var owners = JsonSerializer.Deserialize<Dictionary<ulong, string[]>>(File.ReadAllText(manifest))!;
if (!owners.TryGetValue(address, out var assemblies)) return Error("该地址没有可唯一定位的托管方法定义，不支持此入口。");
if (assemblies.Length != 1) return Error("该地址跨程序集共享；仅凭 VA 无法确定托管上下文。");
var inputs = new NativeInputs(binary, Path.Combine(cache, "script.json"), Path.Combine(cache, "il2cpp.h"),
    Path.Combine(cache, "DummyDll", assemblies[0]), capstone, Environment.GetEnvironmentVariable("CPP2CS_CLANG") ?? "clang", metadata);
using var session = new RecoverySession(inputs);
if (session.Symbols.Unique(address) is null) return Error("该地址缺少唯一的 native 签名，无法确定恢复上下文。");
var result = session.Recover(address);
Console.WriteLine(session.Render(result).TrimEnd());
foreach (var problem in result.Problems) Console.Error.WriteLine($"未恢复：{problem}");
if (args.Length == 5) session.Save(result, args[4]);
return result.Problems.Count == 0 ? 0 : 3;

static int Error(string message) { Console.Error.WriteLine(message); return 2; }
static string Hash(string path)
{
    using var stream = File.OpenRead(path);
    return Convert.ToHexString(SHA256.HashData(stream)).ToLowerInvariant();
}
