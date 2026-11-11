using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.Json.Serialization;

namespace Cpp2CS.Pipeline;

public enum MethodStatus { Complete, Hole }
public sealed record EntryReport(ulong Address, string Kind, string Instance);
public sealed record MethodReport(string Identity, string Name, ulong Entry, EntryReport[] Entries, MethodStatus Status, Hole? Hole);
public sealed record RunSummary(int Methods, int Complete, int Holes, Dictionary<string, int> HolesByLayer,
    Dictionary<string, int> HolesByReason, Dictionary<string, double> LayerSeconds, double ElapsedSeconds, long PeakWorkingSetBytes);
public sealed record RecoveryReport(int FormatVersion, MethodReport[] Methods, RunSummary Summary)
{
    public static string Json<T>(T value)
    {
        var options = new JsonSerializerOptions { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
            Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };
        options.Converters.Add(new JsonStringEnumConverter());
        JsonNode? Sort(JsonNode? node) => node switch
        {
            JsonObject obj => new JsonObject(obj.OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => KeyValuePair.Create(p.Key, Sort(p.Value)))),
            JsonArray array => new JsonArray(array.Select(Sort).ToArray()),
            _ => node?.DeepClone()
        };
        return Sort(JsonSerializer.SerializeToNode(value, options))!.ToJsonString(options) + "\n";
    }
}
