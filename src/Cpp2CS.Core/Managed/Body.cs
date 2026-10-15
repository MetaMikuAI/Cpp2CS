using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

public abstract record ManagedStatement(ulong Address);
public sealed record ManagedAssignment(ulong Address, LocalValue Target, ManagedValue Value) : ManagedStatement(Address);
public sealed record ManagedStore(ulong Address, ManagedValue Target, ManagedValue Value) : ManagedStatement(Address);
public sealed record ManagedCall(ulong Address, ManagedInvocation Invocation, LocalValue? Result, bool Tail) : ManagedStatement(Address);
public sealed record ManagedReturn(ulong Address, ManagedValue? Value) : ManagedStatement(Address);
public sealed record ManagedJump(ulong Address, ManagedEdge Edge) : ManagedStatement(Address);
public sealed record ManagedBranch(ulong Address, ManagedValue Condition, ManagedEdge Taken, ManagedEdge Fallthrough) : ManagedStatement(Address);

/// <summary>边上的赋值同时生效；先求全部源值，再写目标，避免循环中的 φ 交换被覆盖。</summary>
public sealed record ManagedCopy(LocalValue Target, ManagedValue Value);
public sealed record ManagedEdge(ulong Target, IReadOnlyList<ManagedCopy> Copies);
public sealed record ManagedBlock(ulong Address, IReadOnlyList<ManagedStatement> Statements);
public sealed record ManagedBody(MethodRef Method, IReadOnlyList<ManagedBlock> Blocks);
public sealed record RecoveryProblem(ulong Address, string Reason);
public sealed record BodyRecoveryResult(ManagedBody? Body, IReadOnlyList<RecoveryProblem> Problems);
