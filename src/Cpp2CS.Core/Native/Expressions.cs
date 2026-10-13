using Cpp2CS.IR;

namespace Cpp2CS.Native;

public abstract record Expression;
public sealed record NameExpression(string Name) : Expression;
public sealed record CapturedExpression(string Name, Expression Value) : Expression;
public sealed record ConstantExpression(long Value) : Expression
{
    public string? EnumType { get; init; }
    public string? EnumMember { get; init; }
}
public sealed record UnknownExpression(string Reason) : Expression;
public sealed record AddressExpression(ulong Address) : Expression;
public sealed record AddressOfExpression(Expression Target) : Expression
{
    public string? RootType { get; init; }
}
public sealed record StackAddressExpression(long Offset) : Expression;
public sealed record PhiInput(ulong Predecessor, Expression Value);
public sealed record PhiExpression(string Name, string Type, PhiInput[] Inputs) : Expression;
public sealed record MetadataExpression(MetadataReference Reference, bool IsSlot) : Expression;
public sealed record MemberExpression(Expression Receiver, HeaderField Field, string DisplayName, string? ManagedType) : Expression;
public sealed record BinaryExpression(string Operator, Expression Left, Expression Right) : Expression;
public sealed record SliceExpression(Expression Value, int BitOffset, int BitWidth) : Expression;
public sealed record ComposeExpression(Expression[] Parts, int[] BitWidths) : Expression;
public sealed record AggregateExpression(string Type, Expression Bits) : Expression;
public sealed record InvocationExpression(string Name, Expression? Receiver, Expression[] Arguments, bool IsProperty) : Expression;
public sealed record AwaitExpression(Expression Value) : Expression;
public sealed record CastExpression(string Type, Expression Value) : Expression;
public sealed record SourceMemberExpression(Expression Receiver, string Name, string Type) : Expression;
public sealed record ObjectValueExpression(string Type, (string Name, Expression Value)[] Fields) : Expression;
public sealed record LambdaExpression(string[] Parameters, Expression Body, ulong MethodAddress) : Expression;
public sealed record StaticMemberExpression(string Owner, string Name, string Type, bool IsProperty = false) : Expression;
public sealed record NativeValue(Bits Bits, string Type, Expression Expression);
public abstract record Statement(ulong Address);
public sealed record CallStatement(ulong Pc, string Name, Expression[] Arguments, string? Result, string? ReturnType, bool IsInstance, Expression? Receiver, bool IsProperty = false, bool NoReturn = false) : Statement(Pc)
{
    public string? DeclaringType { get; init; }
}
public sealed record StoreStatement(ulong Pc, Expression Target, Expression Value) : Statement(Pc);
public sealed record ThrowStatement(ulong Pc, string Type) : Statement(Pc);
public sealed record ReturnStatement(ulong Pc, Expression? Value) : Statement(Pc);
public sealed record AssignStatement(ulong Pc, string Name, Expression Value, string Type) : Statement(Pc);
public sealed record EvaluateStatement(ulong Pc, Expression Value) : Statement(Pc);
public sealed record DeclareStatement(ulong Pc, string Name, string Type) : Statement(Pc);
public sealed record SetLocalStatement(ulong Pc, string Name, Expression Value) : Statement(Pc);
public sealed record UnresolvedStatement(ulong Pc, string Reason) : Statement(Pc);
public sealed record EnsureMetadataStatement(ulong Pc, ulong Flag, MetadataReference[] References) : Statement(Pc);
public sealed record ConditionalInvokeStatement(ulong Pc, Expression Receiver, Expression[] Arguments) : Statement(Pc);
public sealed record DelegateCacheStatement(ulong Pc, string Name, string Type, MemberExpression Cache, Expression Target, MetadataExpression Method) : Statement(Pc);
public sealed record LiftedBlock(ulong Address, List<Statement> Statements, Expression? Condition, ulong[] Successors);
public sealed record Proof(ulong Address, string Rule, string Detail);
public sealed record LiftResult(NativeMethod Method, Instruction[] Instructions, Dictionary<ulong, LiftedBlock> Blocks,
    List<string> Problems, List<Proof> Proofs, NativeGraph Graph)
{
    public SsaRecovery? Ssa { get; set; }
    public bool IsSourceProjection { get; init; }
    public string? SourceLambdaOrigin { get; init; }
    public FinallyLoop? Finally { get; init; }
    public string? SourceDeclaration { get; init; }
    public string RecoveryPath { get; init; } = "expression";
    [System.Text.Json.Serialization.JsonIgnore] public Symbols? TypeSymbols { get; init; }
}

public sealed class NativeState
{
    public Dictionary<string, NativeValue> Registers { get; } = [];
    public MemoryState Stack { get; set; } = new("entry");
    public Dictionary<long, NativeValue> StackViews { get; } = [];
    public long StackOffset { get; set; }
    public bool StackPointerKnown { get; set; } = true;
    public (NativeValue Left, NativeValue Right)? Comparison { get; set; }
    public string ComparisonKind { get; set; } = "compare";
    public NativeState Copy()
    {
        var copy = new NativeState { Stack = Stack, StackOffset = StackOffset, StackPointerKnown = StackPointerKnown, Comparison = Comparison, ComparisonKind = ComparisonKind };
        foreach (var item in Registers) copy.Registers.Add(item.Key, item.Value);
        foreach (var item in StackViews) copy.StackViews.Add(item.Key, item.Value);
        return copy;
    }
}
