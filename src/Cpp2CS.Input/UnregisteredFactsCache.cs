#nullable enable
using System;
using System.IO;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Lifting;

namespace Cpp2CS.Input;

internal static class UnregisteredFactsCache
{
    private static readonly Lazy<string> Implementation = new(() =>
        HashFile(typeof(ProgramFacts).Assembly.Location) + HashFile(typeof(FactsBuilder).Assembly.Location));

    internal static string Key(string image, string metadata, string implementation, string runtime) =>
        Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes($"unregistered-v1\n{image}\n{metadata}\n{implementation}\n{runtime}")));

    private static string HashFile(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexString(SHA256.HashData(stream));
    }

    public static UnregisteredMethods GetOrBuild(ProgramFacts facts, string metadata, string directory, Action<string>? log)
    {
        if (directory.Length == 0 || directory.Equals("off", StringComparison.OrdinalIgnoreCase))
        {
            log?.Invoke("未注册事实缓存：禁用");
            return UnregisteredMethods.Build(facts, log);
        }
        var key = Key(facts.Model.Image.Sha256, HashFile(metadata), Implementation.Value,
            RuntimeInformation.FrameworkDescription + "/" + RuntimeInformation.ProcessArchitecture + "/frame-slots=" + FunctionLifter.PromoteFrameSlots);
        var path = Path.Combine(directory, "latest.cache");
        var snapshot = Read(path, key, log);
        if (snapshot is not null)
        {
            var restored = UnregisteredMethods.Restore(snapshot, facts);
            log?.Invoke($"未注册事实缓存：命中，{restored.All.Count} 个接受项、{restored.Decisions.Count} 个判定");
            return restored;
        }
        log?.Invoke("未注册事实缓存：未命中，重新分析");
        var result = UnregisteredMethods.Build(facts, log);
        Write(path, key, result.Capture(facts), log);
        return result;
    }

    internal static UnregisteredMethods.Snapshot? Read(string path, string key, Action<string>? log)
    {
        byte[] data;
        try { data = File.ReadAllBytes(path); }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException)
        {
            log?.Invoke($"未注册事实缓存：无法读取（{e.GetType().Name}）");
            return null;
        }
        // 两行固定长度摘要；截断、输入变化或内容损坏均重算，不接受部分结果。
        if (data.Length < 130 || data[64] != '\n' || data[129] != '\n' || Encoding.ASCII.GetString(data, 0, 64) != key
            || Encoding.ASCII.GetString(data, 65, 64) != Convert.ToHexString(SHA256.HashData(data.AsSpan(130)))) return null;
        return JsonSerializer.Deserialize<UnregisteredMethods.Snapshot>(data.AsSpan(130))
            ?? throw new InvalidDataException("未注册事实缓存内容为空");
    }

    internal static void Write(string path, string key, UnregisteredMethods.Snapshot snapshot, Action<string>? log)
    {
        var payload = JsonSerializer.SerializeToUtf8Bytes(snapshot);
        var header = Encoding.ASCII.GetBytes(key + "\n" + Convert.ToHexString(SHA256.HashData(payload)) + "\n");
        var temporary = path + "." + Guid.NewGuid().ToString("N") + ".tmp";
        try
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            using (var stream = File.Create(temporary))
            {
                stream.Write(header);
                stream.Write(payload);
            }
            File.Move(temporary, path, overwrite: true);
            log?.Invoke($"未注册事实缓存：已保存 {header.Length + payload.Length:N0} 字节");
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException)
        {
            log?.Invoke($"未注册事实缓存：无法保存（{e.GetType().Name}）");
        }
        finally
        {
            // 只清理由本次写入创建的临时文件。
            try { File.Delete(temporary); }
            catch (Exception e) when (e is IOException or UnauthorizedAccessException)
            { log?.Invoke($"未注册事实缓存：临时文件未清理（{e.GetType().Name}）"); }
        }
    }
}
