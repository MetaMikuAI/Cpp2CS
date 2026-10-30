
namespace Cpp2CS.Diagnostics;

public sealed record AnalysisStep(string Rule, int InputVersion, int OutputVersion, int InputTypes, int OutputTypes, double Milliseconds)
{
    public string Kind { get; init; } = "analysis";
    public string? Invalidates { get; init; }
}
