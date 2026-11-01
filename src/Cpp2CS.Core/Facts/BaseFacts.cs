
namespace Cpp2CS.Facts;

public sealed record BaseFacts
{
    public ProgramModel Model { get; init; } = null!;
    public CodeMap Code { get; init; } = null!;
    public CodeScan Scan { get; init; } = null!;
    public Registrations Registrations { get; init; } = null!;
    public UsageSlots Usages { get; init; } = null!;
    public RuntimeHelpers Helpers { get; init; } = null!;
    public FieldLayouts Layouts { get; init; } = null!;
    public FactChecks Checks { get; init; } = null!;
    public IReadOnlyDictionary<string, double> Timings { get; init; } = null!;
    public Cpp2CS.Options.RecoveryOptions Options { get; init; } = new();
    public CodeEntry[] EntriesAt(ulong address) => Registrations.At(address);
}
