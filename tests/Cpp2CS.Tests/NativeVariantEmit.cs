using System.Security.Cryptography;
using System.Text.Encodings.Web;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil;

namespace Cpp2CS.Tests;

/// <summary>逐实例写出并回读 CIL；相同定义及指令内容复用已验证的磁盘产物。</summary>
internal static class NativeVariantEmit
{
    [Command("emit-variants", "恢复多入口清单，保留每个入口对应的独立 CIL 证据", Arguments = "<binary> <metadata> <methods.tsv> <output>")]
    public static int Run(string binary, string metadata, string methodList, string output)
    {
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        var skeleton = new Skeleton(facts.Model);
        var emitter = new BodyEmitter(skeleton, types);
        var selected = File.ReadLines(methodList).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t'))
            .Select(p => RecoveryTarget.Find(facts, Convert.ToUInt64(p[0], 16), p[1])).ToArray();
        var batches = selected.GroupBy(t => t.Instance.Method).SelectMany(g => g.Select((t, i) => (Target: t, Batch: i)))
            .GroupBy(p => p.Batch).OrderBy(g => g.Key);
        Directory.CreateDirectory(output);
        var json = new JsonSerializerOptions { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };
        using var writer = new StreamWriter(Path.Combine(output, "recovery.jsonl")) { AutoFlush = true };
        var saved = new Dictionary<(MethodDef Method, string Hash), (string Path, uint Token)>();
        var emitted = 0;
        var bytes = new Dictionary<ulong, long>();
        foreach (var batch in batches)
        {
            var results = batch.Select(p => p.Target.Recover(recovery)).ToArray();
            var problems = emitter.Emit(results.Where(r => r.Body is not null).Select(r => r.Body!));
            var complete = results.Where(r => r.Body is not null && !problems.ContainsKey(r.Body)).ToArray();
            var fingerprints = complete.ToDictionary(r => r, r => Convert.ToHexString(SHA256.HashData(EmittedBodyCheck.Describe(skeleton.Method(r.Method.Method)))));
            foreach (var group in complete.Where(r => !saved.ContainsKey((r.Method.Method, fingerprints[r]))).GroupBy(r => r.Method.Method.Owner.Assembly))
            {
                var path = Path.Combine($"batch-{batch.Key:D2}", group.Key);
                Directory.CreateDirectory(Path.Combine(output, $"batch-{batch.Key:D2}"));
                skeleton.Assembly(group.Key).Write(Path.Combine(output, path));
                using var module = ModuleDefinition.ReadModule(Path.Combine(output, path));
                foreach (var result in group)
                {
                    var token = skeleton.Method(result.Method.Method).MetadataToken.ToUInt32();
                    var method = (MethodDefinition)module.LookupToken(new MetadataToken(token));
                    var hash = Convert.ToHexString(SHA256.HashData(EmittedBodyCheck.Describe(method)));
                    if (hash != fingerprints[result]) throw new InvalidDataException($"{result.Method} 写出回读不一致");
                    saved.Add((result.Method.Method, hash), (path, token));
                }
            }
            foreach (var result in results)
            {
                var success = fingerprints.TryGetValue(result, out var hash);
                var artifact = success ? saved[(result.Method.Method, hash!)] : default;
                var size = checked((long)facts.Code.At(result.Entry)!.Size);
                if (success) { emitted++; bytes[result.Entry] = size; }
                writer.WriteLine(JsonSerializer.Serialize(new
                {
                    address = $"0x{result.Entry:x}", method = result.Method.ToString(), status = success ? "emitted" : result.Body is null ? "hole" : "emit-failed",
                    bytes = size, dependency = false, artifact = artifact.Path, token = artifact.Token, cilHash = hash,
                    holes = result.Holes.Select(h => new { address = $"0x{h.Address:x}", reason = h.Reason }),
                    emitProblem = result.Body is null ? null : problems.GetValueOrDefault(result.Body)?.Message,
                }, json));
            }
            Console.WriteLine($"批次 {batch.Key + 1}，累计写出 {emitted}，独立入口 {bytes.Count}，字节 {bytes.Values.Sum()}");
        }
        Console.WriteLine($"清单 {selected.Length}，写出 {emitted}，不同 CIL 方法体 {saved.Count}；已回读磁盘核对，尚未验证执行等价");
        return emitted == selected.Length ? 0 : 1;
    }
}
