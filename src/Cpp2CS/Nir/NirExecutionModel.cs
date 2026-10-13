using System.Collections.Immutable;
using System.Numerics;

namespace Cpp2CS.Nir;

public sealed record NirRuntimeValue(NirType Type, BigInteger Bits, string? Function = null, NirExceptionToken? Exception = null)
{
    public static NirRuntimeValue Integer(int width, BigInteger value) => new(new NirBitsType(width), value);
    public static NirRuntimeValue Address(string space, int width, BigInteger value) => new(new NirAddressType(space, width), value);
    public static NirRuntimeValue FunctionReference(string name, NirSignature signature,
        NirOutcomes outcomes = NirOutcomes.Return | NirOutcomes.Fault | NirOutcomes.Diverge) => new(new NirFunctionType(signature, outcomes), 0, name);
}
public enum NirExecutionStatus { Returned, Faulted, Terminated, BudgetExceeded, MissingInput, MissingExternal, ContractViolation, InvalidModule, InvalidInput, Unwound }
public sealed record NirExecutionOptions(long MaxSteps = 100_000, int MaxDepth = 1024, int MaxAllocationBytes = 1024 * 1024, NirBlockId? Entry = null);
public sealed record NirExecutionEvent(long Sequence, string Kind, string Function, string? Detail = null)
{
    public NirMemoryObservation? Memory { get; init; }
}
public sealed record NirExecutionResult(NirExecutionStatus Status, ImmutableArray<NirRuntimeValue> Values,
    long Effect, long Steps, string? Detail, ImmutableArray<NirDiagnostic> Diagnostics, ImmutableArray<NirExecutionEvent> Events,
    NirRuntimeValue? Exception = null);
public enum NirExternalOutcome { Return, Fault, Terminate, Unwind }
public sealed record NirExternalResult(NirExternalOutcome Outcome, ImmutableArray<NirRuntimeValue> Values,
    string? Detail = null, NirRuntimeValue? Exception = null)
{
    public static NirExternalResult Returned(params NirRuntimeValue[] values) => new(NirExternalOutcome.Return, [.. values]);
    public static NirExternalResult Unwound(NirRuntimeValue exception) => new(NirExternalOutcome.Unwind, [], Exception: exception);
}

public sealed class NirExternalInvocation
{
    private readonly NirMemory memory;
    private readonly Dictionary<NirEnvironmentField, BigInteger> environment;
    private readonly Func<NirRuntimeValue> createException;
    internal string? Violation { get; private set; }
    public NirExternalContract Contract { get; }
    public ImmutableArray<NirRuntimeValue> Arguments { get; }
    internal NirExternalInvocation(NirExternalContract contract, ImmutableArray<NirRuntimeValue> arguments, NirMemory memory,
        Dictionary<NirEnvironmentField, BigInteger> environment, Func<NirRuntimeValue> createException)
        => (Contract, Arguments, this.memory, this.environment, this.createException) = (contract, arguments, memory, environment, createException);
    public NirRuntimeValue CreateException() => createException();
    public NirEnvironmentResult ReadEnvironment(NirEnvironmentField field)
    {
        if (!Contract.Effects.HasFlag(NirExternalEffects.Environment))
        { Violation = "ExternalEnvironmentOutsideContract"; return new(0, Violation); }
        if (!environment.TryGetValue(field, out var value)) return new(0, "MissingEnvironmentInput");
        if (!NirEnvironmentContract.Valid(field, value)) return new(0, "InvalidEnvironmentInput");
        return new(value);
    }
    public NirEnvironmentResult WriteEnvironment(NirEnvironmentField field, BigInteger value)
    {
        if (!Contract.Effects.HasFlag(NirExternalEffects.Environment))
        { Violation = "ExternalEnvironmentOutsideContract"; return new(0, Violation); }
        if (!NirEnvironmentContract.Valid(field, value))
        { Violation = "InvalidExternalEnvironmentWrite"; return new(0, Violation); }
        environment[field] = value;
        return new(value);
    }
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
    public Dictionary<NirEnvironmentField, BigInteger> Environment { get; } = [];
    public List<NirExecutionEvent> Events { get; } = [];
    public long Effect { get; private set; }
    private long exceptionId;
    public NirRuntimeValue CreateException() => new(NirExceptionType.Instance, 0, Exception: new(checked(++exceptionId), this));
    public NirExecutionContext(NirModule module)
    {
        var validation = NirValidator.Validate(module);
        if (!validation.IsValid) throw new ArgumentException("NIR context requires a valid module", nameof(module));
        Module = module;
        Memory = new(module);
    }
    internal NirRuntimeValue Token() => new(NirEffectType.Instance, Effect);
    internal void Advance(string kind, string function, string? detail = null, NirMemoryObservation? memory = null)
    {
        Effect++;
        Events.Add(new(Effect, kind, function, detail) { Memory = memory });
    }
}
