using System.Text.Json.Serialization;

namespace Cpp2CS.Diagnostics;

public interface IDiagnosticSink
{
    void Write(string category, ulong entry, string message);
}

public sealed record DiagnosticOptions
{
    public bool Emit { get; init; }
    public bool Exceptions { get; init; }
    public string? SourceDump { get; init; }
    public IReadOnlySet<ulong> Frames { get; init; } = new HashSet<ulong>();
    public IReadOnlySet<ulong> Typing { get; init; } = new HashSet<ulong>();
    [JsonIgnore] public IDiagnosticSink? Sink { get; init; }
    public void Write(string category, ulong entry, string message) => Sink?.Write(category, entry, message);
}
