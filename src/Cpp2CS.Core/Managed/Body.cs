namespace Cpp2CS.Managed;

/// <summary>边上的赋值同时生效：先求全部源值，再写目标。</summary>
public sealed record ManagedCopy(LocalValue Target, ManagedValue Value);
public sealed record ManagedEdge(ulong Target, IReadOnlyList<ManagedCopy> Copies);
public sealed record ManagedBlock(ulong Address, IReadOnlyList<ManagedStatement> Statements);
public enum ManagedRegionKind { Catch, Fault }
/// <summary>块序来自语句图见证；Exception 仅供 catch 的入口保存当前异常对象。</summary>
public sealed record ManagedRegion(IReadOnlyList<ulong> Try, ulong HandlerEntry, IReadOnlyList<ulong> Handler,
    LocalValue? Exception, ManagedRegionKind Kind)
{
    /// <summary>catch 的类型；null 为 System.Exception（恢复出的区域一律如此，C# 输出整理可把类型判断还原成带类型的 catch）。</summary>
    public TypeRef? CatchType { get; init; }
}
public sealed record ManagedBody(MethodRef Method, IReadOnlyList<ManagedBlock> Blocks)
{
    public IReadOnlyList<ManagedRegion> Regions { get; init; } = [];
}
