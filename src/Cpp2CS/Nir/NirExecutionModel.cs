using System.Collections.Immutable;
using System.Numerics;

namespace Cpp2CS.Nir;

public sealed record NirRuntimeValue(NirType Type, BigInteger Bits, string? Function = null)
{
    public static NirRuntimeValue Integer(int width, BigInteger value) => new(new NirBitsType(width), value);
    public static NirRuntimeValue Address(string space, int width, BigInteger value) => new(new NirAddressType(space, width), value);
    public static NirRuntimeValue FunctionReference(string name, NirSignature signature) => new(new NirFunctionType(signature), 0, name);
}
public enum NirExecutionStatus { Returned, Faulted, Terminated, BudgetExceeded, MissingInput, MissingExternal, ContractViolation, InvalidModule, InvalidInput }
public sealed record NirExecutionOptions(long MaxSteps = 100_000, int MaxDepth = 1024, int MaxAllocationBytes = 1024 * 1024, NirBlockId? Entry = null);
public sealed record NirExecutionEvent(long Sequence, string Kind, string Function, string? Detail = null);
public sealed record NirExecutionResult(NirExecutionStatus Status, ImmutableArray<NirRuntimeValue> Values,
    long Effect, long Steps, string? Detail, ImmutableArray<NirDiagnostic> Diagnostics, ImmutableArray<NirExecutionEvent> Events);
public enum NirExternalOutcome { Return, Fault, Terminate }
public sealed record NirExternalResult(NirExternalOutcome Outcome, ImmutableArray<NirRuntimeValue> Values, string? Detail = null)
{
    public static NirExternalResult Returned(params NirRuntimeValue[] values) => new(NirExternalOutcome.Return, [.. values]);
}

public sealed class NirExternalInvocation
{
    private readonly NirMemory memory;
    internal string? Violation { get; private set; }
    public NirExternalContract Contract { get; }
    public ImmutableArray<NirRuntimeValue> Arguments { get; }
    internal NirExternalInvocation(NirExternalContract contract, ImmutableArray<NirRuntimeValue> arguments, NirMemory memory)
        => (Contract, Arguments, this.memory) = (contract, arguments, memory);
    public NirMemoryResult Read(string space, BigInteger address, int length)
    {
        if (!Contract.Effects.HasFlag(NirExternalEffects.ReadMemory))
        { Violation = "ExternalReadOutsideContract"; return new([], Violation); }
        return memory.Read(space, address, length);
    }
    public NirMemoryResult Write(string space, BigInteger address, ImmutableArray<byte> bytes)
    {
        if (!Contract.Effects.HasFlag(NirExternalEffects.WriteMemory))
        { Violation = "ExternalWriteOutsideContract"; return new([], Violation); }
        return memory.Write(space, address, bytes);
    }
}

public sealed class NirExecutionContext
{
    public NirModule Module { get; }
    public NirMemory Memory { get; }
    public Dictionary<string, Func<NirExternalInvocation, NirExternalResult>> Externals { get; } = new(StringComparer.Ordinal);
    public Queue<BigInteger> Choices { get; } = new();
    public List<NirExecutionEvent> Events { get; } = [];
    public long Effect { get; private set; }
    public NirExecutionContext(NirModule module)
    {
        var validation = NirValidator.Validate(module);
        if (!validation.IsValid) throw new ArgumentException("NIR context requires a valid module", nameof(module));
        Module = module;
        Memory = new(module);
    }
    internal NirRuntimeValue Token() => new(NirEffectType.Instance, Effect);
    internal void Advance(string kind, string function, string? detail = null)
    {
        Effect++;
        Events.Add(new(Effect, kind, function, detail));
    }
}
