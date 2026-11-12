using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.Json.Serialization;

namespace Cpp2CS.Pipeline;

/// <summary>NoBody：方法的声明不允许 CIL 方法体，不是恢复对象，也不是洞。</summary>
public enum MethodStatus { Complete, Hole, NoBody }
public sealed record EntryReport(ulong Address, string Kind, string Instance);
public sealed record MethodReport(string Identity, string Name, ulong Entry, EntryReport[] Entries, MethodStatus Status, Hole? Hole)
{
    public Cpp2CS.Managed.GenericWitnessCoverage? WitnessCoverage { get; init; }
    public bool HasValueTypeInstance { get; init; }
    public EntryReport? ValueWitness { get; init; }
}
public sealed record RunSummary(int Methods, int Complete, int Holes, Dictionary<string, int> HolesByLayer,
    Dictionary<string, int> HolesByReason, Dictionary<string, double> LayerSeconds, double ElapsedSeconds, long PeakWorkingSetBytes)
{
    public int NoBody { get; init; }
    /// <summary>输出层契约失败的方法；非空表示恢复层有程序错误，命令以失败退出。</summary>
    public string[] ContractFailures { get; init; } = [];
    /// <summary>恢复过程中抛出异常的方法；非空表示有程序错误，命令以失败退出。</summary>
    public string[] ProgramErrors { get; init; } = [];
    public Dictionary<string, int> RuntimeFunctionsByEvidence { get; init; } = [];
}
public sealed record RecoveryReport(int FormatVersion, MethodReport[] Methods, RunSummary Summary)
{
    public SourceReport? Source { get; init; }

    private static JsonSerializerOptions Options()
    {
        var options = new JsonSerializerOptions { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
            Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };
        options.Converters.Add(new JsonStringEnumConverter());
        return options;
    }
    private static JsonNode? Sort(JsonNode? node) => node switch
    {
        JsonObject obj => new JsonObject(obj.OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => KeyValuePair.Create(p.Key, Sort(p.Value)))),
        JsonArray array => new JsonArray(array.Select(Sort).ToArray()),
        _ => node?.DeepClone()
    };
    public static string Json<T>(T value)
    {
        var options = Options();
        return Sort(JsonSerializer.SerializeToNode(value, options))!.ToJsonString(options) + "\n";
    }
    /// <summary>按方法写出并定期提交缓冲，不在内存中构造全量报告的 JSON 树或字符串。</summary>
    public static void Write(Stream destination, RecoveryReport report)
    {
        var options = Options();
        using var writer = new Utf8JsonWriter(destination, new JsonWriterOptions { Indented = true, Encoder = options.Encoder });
        void Value<T>(T value)
        {
            var node = Sort(JsonSerializer.SerializeToNode(value, options));
            if (node is null) writer.WriteNullValue(); else node.WriteTo(writer, options);
            if (writer.BytesPending >= 64 * 1024) writer.Flush();
        }
        void Array<T>(string name, IEnumerable<T> values)
        {
            writer.WriteStartArray(name);
            foreach (var value in values) Value(value);
            writer.WriteEndArray();
        }
        writer.WriteStartObject();
        writer.WriteNumber("format_version", report.FormatVersion);
        Array("methods", report.Methods);
        writer.WritePropertyName("source");
        if (report.Source is not { } source) writer.WriteNullValue();
        else
        {
            writer.WriteStartObject(); writer.WriteNumber("files", source.Files);
            Array("methods", source.Methods); Array("types", source.Types); writer.WriteEndObject();
        }
        writer.WritePropertyName("summary"); Value(report.Summary);
        writer.WriteEndObject(); writer.Flush(); destination.WriteByte((byte)'\n');
    }
}
