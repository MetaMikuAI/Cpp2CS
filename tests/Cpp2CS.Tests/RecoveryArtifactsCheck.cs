using System.Security.Cryptography;
using System.Text.Json;
using Cpp2CS.Output;
using Mono.Cecil;

namespace Cpp2CS.Tests;

internal static class RecoveryArtifactsCheck
{
    private static Dictionary<string, JsonElement> Rows(string directory, string file) => File.ReadLines(Path.Combine(directory, file))
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToDictionary(r => r.GetProperty("address").GetString() + "\t" + r.GetProperty("method").GetString());

    /// <summary>
    /// 逐键比较 recovery.jsonl 的行集合、行次序与每行全部字段（新增字段自动纳入比较），并比较 src/**/*.cs 的 SHA256。
    /// 洞按顺序随所在行一起比较（address、reason、derived、code、category、id、causeId）。
    /// </summary>
    [Command("recovery-delta", "逐方法比较 recovery.jsonl 的全部字段与行次序，以及 C# 文件", Arguments = "<before> <after>")]
    public static int Delta(string before, string after)
    {
        var log = new DeltaLog("recovery-delta");
        Jsonl.CompareKeyed(log, "recovery.jsonl", before, after);
        static Dictionary<string, string> Sources(string directory) => Directory.Exists(Path.Combine(directory, "src"))
            ? Directory.GetFiles(Path.Combine(directory, "src"), "*.cs", SearchOption.AllDirectories)
                .ToDictionary(p => Path.GetRelativePath(directory, p), p => Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(p)))) : [];
        var oldFiles = Sources(before); var newFiles = Sources(after);
        foreach (var file in oldFiles.Keys.Except(newFiles.Keys)) log.Fail("C# 文件丢失", file);
        foreach (var file in newFiles.Keys.Except(oldFiles.Keys)) log.Fail("C# 文件新增", file);
        foreach (var file in oldFiles.Keys.Intersect(newFiles.Keys).Order(StringComparer.Ordinal))
        {
            log.Compared++;
            if (oldFiles[file] != newFiles[file]) log.Fail("C# 文件内容", file);
        }
        return log.Finish();
    }

    [Command("artifact-consistency", "核对发布清单、逐方法磁盘 CIL 和运行产物摘要", Arguments = "<output>")]
    public static int Consistency(string output) => Check(output, completeRun: true);

    [Command("publication-consistency", "核对发布清单、状态与磁盘 CIL，不判断整个运行是否完成", Arguments = "<output>")]
    public static int Publications(string output) => Check(output, completeRun: false);

    private static int Check(string output, bool completeRun)
    {
        var a = new Assertions();
        var reports = Rows(output, "recovery.jsonl");
        var publications = Rows(output, "publication.jsonl");
        var emitted = File.ReadLines(Path.Combine(output, "emitted.tsv")).Select(l => l.Split('\t')).Select(r => r[3] + "\t" + r[4]).ToHashSet();
        a.True(emitted.SetEquals(reports.Where(p => p.Value.GetProperty("status").GetString() == "emitted").Select(p => p.Key)), "emitted.tsv 与状态一致");
        a.True(publications.Keys.ToHashSet().SetEquals(reports.Keys), "全部方法都有发布记录");
        foreach (var group in publications.GroupBy(p => p.Value.GetProperty("assembly").GetString()!))
        {
            using var module = ModuleDefinition.ReadModule(Path.Combine(output, "assemblies", group.Key));
            foreach (var (key, row) in group)
            {
                var method = (MethodDefinition)module.LookupToken((int)row.GetProperty("token").GetUInt32());
                a.Equal(row.GetProperty("cil").GetString(), method.HasBody ? Convert.ToHexString(SHA256.HashData(CilBodyFingerprint.Describe(method))) : null, key + " / 发布体");
            }
        }
        if (!completeRun) return a.Finish("publication-consistency");
        var manifest = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "run.json")));
        a.Equal("complete", manifest.GetProperty("status").GetString(), "运行完成");
        foreach (var artifact in manifest.GetProperty("artifacts").EnumerateObject())
            a.Equal(artifact.Value.GetString(), Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(Path.Combine(output, artifact.Name)))), artifact.Name);
        return a.Finish("artifact-consistency");
    }
}
