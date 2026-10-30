
namespace Cpp2CS.Pipeline;

/// <summary>命令入口读取一次兼容环境选项，再向各阶段传递。</summary>
internal static class RecoveryEnvironment
{
    internal static RecoveryOptions Read() => new()
    {
        PromoteFrameSlots = Environment.GetEnvironmentVariable("CPP2CS_FRAME_SLOTS") != "off",
        Readability = ReadabilityRewriter.Parse(Environment.GetEnvironmentVariable("CPP2CS_READABILITY")),
        FactCacheDirectory = Environment.GetEnvironmentVariable("CPP2CS_FACT_CACHE"),
        Diagnostics = new()
        {
            Emit = Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1",
            Exceptions = Environment.GetEnvironmentVariable("CPP2CS_EH_DEBUG") == "1",
            SourceDump = Environment.GetEnvironmentVariable("CPP2CS_SOURCE_DUMP"),
            Frames = Entries(Environment.GetEnvironmentVariable("CPP2CS_FRAME_DEBUG")),
            Typing = Entries(Environment.GetEnvironmentVariable("CPP2CS_TYPING_TRACE")),
            Sink = new ConsoleSink(),
        },
    };

    private static IReadOnlySet<ulong> Entries(string? text) => (text ?? "").Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries)
        .Select(value => Convert.ToUInt64(value.StartsWith("0x", StringComparison.Ordinal) ? value[2..] : value, 16)).ToHashSet();

    private sealed class ConsoleSink : IDiagnosticSink
    {
        public void Write(string category, ulong entry, string message) => Console.Error.WriteLine(message);
    }
}
