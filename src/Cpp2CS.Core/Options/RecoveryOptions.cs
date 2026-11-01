
namespace Cpp2CS.Options;

[Flags]
public enum ReadabilityRules { None = 0, Int = 1, Null = 2, Goto = 4 }

/// <summary>一次恢复的显式选项；核心层不读取进程环境。</summary>
public sealed record RecoveryOptions
{
    public bool PromoteFrameSlots { get; init; } = true;
    public ReadabilityRules Readability { get; init; } = ReadabilityRules.Int | ReadabilityRules.Null;
    public string? FactCacheDirectory { get; init; }
    /// <summary>显式复用同一份事实快照；核对输入与选项，但不随恢复器代码变化失效。</summary>
    public string? FactCacheFile { get; init; }
    public DiagnosticOptions Diagnostics { get; init; } = new();
}
