using System.Collections.Immutable;
using Cpp2CS.Nir;

namespace Cpp2CS.Recovery;

public sealed record NirRecoveryOptions(int MaxInstructions = 10_000, int MaxNormalizationRounds = 64,
    bool AssumeNormalExecution = false, bool AssumePrivateValidFrames = false,
    FunctionGraphOptions? GraphOptions = null, bool AssumeSequentialMemory = false);

public sealed record NirRecoveryDiagnostic(ulong Address, string Code, string Message);
public sealed record NirRecoveryStatistics(int MachineBlocks, int MachineValues, int NirBlocks,
    int NirOperations, int EliminatedFrameAccesses, int Calls, int NormalizationRounds);
public sealed record NirRecoveryEvidence(string Rule, ulong Address, int? Operation, string Detail);
public sealed record NirFunctionRecovery(DerivedFunctionGraph Graph, NirFunction? Function,
    ImmutableArray<NirRecoveryDiagnostic> Diagnostics, ImmutableArray<NirRecoveryEvidence> Evidence,
    NirRecoveryStatistics Statistics)
{
    public bool Complete => Function is not null && Diagnostics.IsEmpty;
}
public sealed record NirRecoveryResult(NirModule Module, ImmutableArray<NirFunctionRecovery> Functions)
{
    public bool Complete => Functions.All(function => function.Complete);
    public IEnumerable<NirRecoveryDiagnostic> Gaps => Functions.SelectMany(function => function.Diagnostics);
}
