namespace Cpp2CS.Managed;

public abstract record ManagedStatement(ulong Address);
public sealed record ManagedAssignment(ulong Address, LocalValue Target, ManagedValue Value) : ManagedStatement(Address);
/// <summary>写入字段、静态字段或数组元素。</summary>
public sealed record ManagedStore(ulong Address, ManagedValue Target, ManagedValue Value) : ManagedStatement(Address);
/// <summary>调用；Tail 为真时调用后立即以其结果返回。</summary>
public sealed record ManagedCall(ulong Address, ManagedInvocation Invocation, LocalValue? Result, bool Tail) : ManagedStatement(Address)
{
    /// <summary>由内联认回（内联认回）得到：原生代码在此处内联了被调方法，执行对照按被调方法的方法体透明执行。</summary>
    public bool Inlined { get; init; }
}
public sealed record ManagedReturn(ulong Address, ManagedValue? Value) : ManagedStatement(Address);
public sealed record ManagedJump(ulong Address, ManagedEdge Edge) : ManagedStatement(Address);
public sealed record ManagedBranch(ulong Address, ManagedValue Condition, ManagedEdge Taken, ManagedEdge Fallthrough) : ManagedStatement(Address);
/// <summary>按 int32 下标跳转（跳转表）：Cases[i] 是下标 i 的出边；下标越界不可达（原生代码在前驱中检查了上界）。</summary>
public sealed record ManagedSwitch(ulong Address, ManagedValue Index, IReadOnlyList<ManagedEdge> Cases) : ManagedStatement(Address);
/// <summary>抛出 Exception（引用类型的值）。</summary>
public sealed record ManagedThrow(ulong Address, ManagedValue Exception) : ManagedStatement(Address);
public sealed record ManagedRethrow(ulong Address) : ManagedStatement(Address);
public sealed record ManagedEndFault(ulong Address) : ManagedStatement(Address);
/// <summary>await Task（只出现在 源码视图提升 提升出的 C# 输出方法体里）；Result 为 null 表示丢弃结果或无结果。</summary>
public sealed record ManagedAwait(ulong Address, ManagedValue Task, LocalValue? Result) : ManagedStatement(Address);
/// <summary>部分方法体中未恢复的语句；Terminal 为真时它结束所在的块（未恢复的终结语句）。</summary>
public sealed record ManagedHole(ulong Address, string Reason, bool Terminal) : ManagedStatement(Address);
/// <summary>Condition 成立时以无参构造函数 Exception 新建异常并抛出（L2 的判空、越界与 ThrowIf 未被后续访问吸收时）。</summary>
public sealed record ManagedCheck(ulong Address, ManagedValue Condition, MethodRef Exception) : ManagedStatement(Address);
