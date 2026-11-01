using System.Diagnostics;
using System.Security.Cryptography;
using System.Text.Encodings.Web;
using System.Text.Json;

namespace Cpp2CS.Pipeline;

/// <summary>阶段完成后发布清单；中断的运行保留 incomplete，不冒充完整产物。</summary>
internal sealed class RunManifest
{
    private sealed record Stage(string Name, string Status, double Seconds);
    private static readonly JsonSerializerOptions Json = new() { WriteIndented = true, Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };
    private readonly RecoveryRequest request;
    private readonly Dictionary<string, string> inputs = new(StringComparer.Ordinal);
    private readonly Dictionary<string, string> implementation = new(StringComparer.Ordinal);
    private readonly List<Stage> stages = [];
    private readonly Stopwatch elapsed = Stopwatch.StartNew();
    private long stageStarted;
    private string status = "incomplete";
    private readonly string path;
    private readonly string runId = Guid.NewGuid().ToString("N");

    public RunManifest(RecoveryRequest request)
    {
        this.request = request;
        if (Directory.Exists(request.Output) && Directory.EnumerateFileSystemEntries(request.Output).Any())
            throw new IOException($"输出目录非空，不能把不同运行的产物混合：{request.Output}");
        Directory.CreateDirectory(request.Output);
        path = Path.Combine(request.Output, "run.json");
        inputs["binary"] = Hash(request.Binary);
        inputs["metadata"] = Hash(request.Metadata);
        foreach (var (key, file) in new[] { ("methods", request.Methods), ("verifiedAccessors", request.VerifiedAccessors), ("rejectedAccessors", request.RejectedAccessors) })
            if (file is not null) inputs[key] = Hash(file);
        foreach (var assembly in new[] { typeof(RunManifest).Assembly, typeof(Input.FactsBuilder).Assembly,
            typeof(Recovery.MethodRecovery).Assembly, typeof(Output.BodyEmitter).Assembly,
            typeof(Cpp2CS.Extensions.Readability.FullBodyEmitter).Assembly, typeof(ICSharpCode.Decompiler.DecompilerSettings).Assembly })
            implementation[assembly.GetName().Name!] = Hash(assembly.Location);
        Save();
    }

    public T Step<T>(string name, Func<T> action)
    {
        Begin(name);
        var value = action();
        End();
        return value;
    }

    public void Begin(string name)
    {
        if (stages.LastOrDefault()?.Status == "running") throw new InvalidOperationException("前一阶段尚未完成");
        stages.Add(new(name, "running", 0));
        stageStarted = Stopwatch.GetTimestamp();
        Save();
    }

    public void End()
    {
        if (stages.Count == 0 || stages[^1].Status != "running") throw new InvalidOperationException("没有正在运行的阶段");
        stages[^1] = stages[^1] with { Status = "complete", Seconds = Stopwatch.GetElapsedTime(stageStarted).TotalSeconds };
        Save();
    }

    public void Complete(RecoveryRunResult result)
    {
        if (stages.Any(s => s.Status != "complete")) throw new InvalidOperationException("不能发布未完成的运行");
        status = "complete";
        Save(result);
    }

    private void Save(RecoveryRunResult? result = null)
    {
        var artifacts = status == "complete" ? Directory.EnumerateFiles(request.Output, "*", SearchOption.AllDirectories)
            .Where(f => f != path && !f.EndsWith(".tmp", StringComparison.Ordinal))
            .Order(StringComparer.Ordinal).ToDictionary(f => Path.GetRelativePath(request.Output, f).Replace('\\', '/'), Hash) : null;
        var text = JsonSerializer.Serialize(new
        {
            schema = 1,
            runId,
            status,
            request,
            inputs,
            implementation,
            factSnapshot = request.Options.FactCacheFile is { } cache && File.Exists(cache) ? Hash(cache) : null,
            stages,
            seconds = elapsed.Elapsed.TotalSeconds,
            peakWorkingSet = Process.GetCurrentProcess().PeakWorkingSet64,
            outcome = result is null ? null : new { result.SelectedMethods, result.EmittedMethods, result.EmitFailures, result.PartialMethods },
            validation = new { compile = "not-run", ilverify = "not-run", execution = "not-run" },
            artifacts,
        }, Json);
        var temporary = path + "." + runId + ".tmp";
        File.WriteAllText(temporary, text);
        File.Move(temporary, path, overwrite: true);
    }

    private static string Hash(string file)
    {
        using var stream = File.OpenRead(file);
        return Convert.ToHexString(SHA256.HashData(stream));
    }
}
