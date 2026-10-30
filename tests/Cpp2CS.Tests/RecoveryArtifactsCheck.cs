using System.Security.Cryptography;
using System.Text.Json;
using Cpp2CS.Output;
using Mono.Cecil;

namespace Cpp2CS.Tests;

internal static class RecoveryArtifactsCheck
{
    private static Dictionary<string, JsonElement> Rows(string directory, string file) => File.ReadLines(Path.Combine(directory, file))
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToDictionary(r => r.GetProperty("address").GetString() + "\t" + r.GetProperty("method").GetString());

    [Command("recovery-delta", "逐方法比较状态、洞和 C# 文件，忽略计时与新增诊断字段", Arguments = "<before> <after>")]
    public static int Delta(string before, string after)
    {
        var previous = Rows(before, "recovery.jsonl");
        var current = Rows(after, "recovery.jsonl");
        var a = new Assertions();
        a.True(previous.Keys.ToHashSet().SetEquals(current.Keys), "方法集合相同");
        foreach (var key in previous.Keys.Intersect(current.Keys))
        {
            var left = previous[key]; var right = current[key];
            foreach (var field in new[] { "status", "bytes", "dependency", "bodySource", "declaration", "platformImport", "accessorProof", "emitProblem", "partial", "statements", "regions", "features" })
                a.Equal(left.TryGetProperty(field, out var l) ? l.GetRawText() : "null", right.TryGetProperty(field, out var r) ? r.GetRawText() : "null", key + " / " + field);
            string Holes(JsonElement row) => JsonSerializer.Serialize(row.GetProperty("holes").EnumerateArray().Select(h => new
            {
                address = h.GetProperty("address"), reason = h.GetProperty("reason"), derived = h.GetProperty("derived"),
                code = h.GetProperty("code"), id = h.GetProperty("id"), causeId = h.GetProperty("causeId"),
            }));
            a.Equal(Holes(left), Holes(right), key + " / 洞");
        }
        static Dictionary<string, string> Sources(string directory) => Directory.Exists(Path.Combine(directory, "src"))
            ? Directory.GetFiles(Path.Combine(directory, "src"), "*.cs", SearchOption.AllDirectories)
                .ToDictionary(p => Path.GetRelativePath(directory, p), p => Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(p)))) : [];
        var oldFiles = Sources(before); var newFiles = Sources(after);
        a.True(oldFiles.Keys.ToHashSet().SetEquals(newFiles.Keys), "C# 文件集合相同");
        foreach (var file in oldFiles.Keys.Intersect(newFiles.Keys)) a.Equal(oldFiles[file], newFiles[file], file);
        Console.WriteLine($"恢复记录 {previous.Count}；C# 文件 {oldFiles.Count}");
        return a.Finish("recovery-delta");
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
