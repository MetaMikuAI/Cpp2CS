using System.Security.Cryptography;
using System.Text.Json;

namespace Cpp2CS.Pipeline;

/// <summary>
/// 从产物目录的 run.json 复原当初的恢复请求，供执行对照按同一 profile 的阶段表重新写出。
/// 运行选项取当前环境（与 recover 相同的读取方式）加上记录的事实快照；与记录不符、或输入文件的哈希不符时拒绝，
/// 不在不同输入或选项下“复现”产物。
/// </summary>
internal static class RunRequest
{
    public static RecoveryRequest Read(string output)
    {
        using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "run.json")));
        var root = document.RootElement;
        if (root.GetProperty("status").GetString() != "complete") throw new InvalidDataException($"{output}：运行未完成");
        var recorded = root.GetProperty("request");
        string? Text(string name) => recorded.GetProperty(name).ValueKind == JsonValueKind.Null ? null : recorded.GetProperty(name).GetString();
        string[]? List(string name) => recorded.GetProperty(name).ValueKind == JsonValueKind.Null ? null
            : recorded.GetProperty(name).EnumerateArray().Select(e => e.GetString()!).ToArray();
        var recordedOptions = recorded.GetProperty("Options");
        var options = RecoveryEnvironment.Read() with
        {
            FactCacheFile = recordedOptions.GetProperty("FactCacheFile").ValueKind == JsonValueKind.Null ? null : recordedOptions.GetProperty("FactCacheFile").GetString(),
        };
        if (options.PromoteFrameSlots != recordedOptions.GetProperty("PromoteFrameSlots").GetBoolean()
            || (int)options.Readability != recordedOptions.GetProperty("Readability").GetInt32())
            throw new InvalidDataException($"{output}：当前环境的 CPP2CS_FRAME_SLOTS 或 CPP2CS_READABILITY 与产物记录不同");
        var request = new RecoveryRequest(Text("Binary")!, Text("Metadata")!, Text("Output")!)
        {
            Options = options,
            Profile = Text("Profile")!,
            All = recorded.GetProperty("All").GetBoolean(),
            Namespaces = List("Namespaces") ?? [],
            Assemblies = List("Assemblies"),
            Methods = Text("Methods"),
            Limit = recorded.GetProperty("Limit").GetInt32(),
            Jobs = recorded.GetProperty("Jobs").GetInt32(),
            NoSource = recorded.GetProperty("NoSource").GetBoolean(),
            SourceLayout = Text("SourceLayout")!,
            VerifiedAccessors = Text("VerifiedAccessors"),
            RejectedAccessors = Text("RejectedAccessors"),
        };
        var inputs = root.GetProperty("inputs");
        foreach (var (key, file) in new[] { ("binary", request.Binary), ("metadata", request.Metadata), ("methods", request.Methods),
            ("verifiedAccessors", request.VerifiedAccessors), ("rejectedAccessors", request.RejectedAccessors) })
        {
            if (file is null) continue;
            if (Hash(file) != inputs.GetProperty(key).GetString()) throw new InvalidDataException($"{output}：输入 {key}（{file}）与产物记录的哈希不同");
        }
        if (root.GetProperty("factSnapshot").GetString() is { } snapshot && (options.FactCacheFile is null || Hash(options.FactCacheFile) != snapshot))
            throw new InvalidDataException($"{output}：事实快照与产物记录不同");
        return request;
    }

    private static string Hash(string file)
    {
        using var stream = File.OpenRead(file);
        return Convert.ToHexString(SHA256.HashData(stream));
    }
}
