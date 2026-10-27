using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>带托管类型的值。Width 是值在机器上的位宽（比较结果为 1，bool 字段为 8）。</summary>
public abstract record ManagedValue(TypeRef Type, int Width);
/// <summary>方法参数；Index 为 -1 表示 this。</summary>
public sealed record ArgumentValue(int Index, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>SSA 变量对应的局部变量。</summary>
public sealed record LocalValue(Variable Variable, TypeRef Type, int Width) : ManagedValue(Type, Width);
/// <summary>Bits 保存原始位型，浮点常量也不经过数值转换。</summary>
public sealed record ConstantValue(ulong Bits, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record StringValue(string Text, TypeRef Type) : ManagedValue(Type, 64);
public sealed record TypeHandleValue(TypeRef Target, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record NewArrayValue(ArrayRef ArrayType, ManagedValue Length) : ManagedValue(ArrayType, 64);
public sealed record NewObjectValue(MethodRef Constructor, IReadOnlyList<ManagedValue> Arguments) : ManagedValue(Constructor.DeclaringType, 64)
{
    /// <summary>原生代码内联了这个构造函数：执行对照按构造函数的方法体透明执行。</summary>
    public bool Transparent { get; init; }
}
public enum DelegateBinding { Static, ClosedInstance, VirtualInstance }
/// <summary>方法身份只来自直接 Method 符号；不表示虚表选择、开放绑定或方法身份的 φ。</summary>
public sealed record DelegateValue(DefinitionRef DelegateType, ManagedValue Target, MethodRef Method, DelegateBinding Binding) : ManagedValue(DelegateType, 64);
/// <summary>把 Operand 按 Boxed 类型装箱（Boxed 决定对象的运行时类型，与 Operand 的整数符号无关）。</summary>
public sealed record BoxValue(ManagedValue Operand, TypeRef Boxed, TypeRef ObjectType) : ManagedValue(ObjectType, 64);
/// <summary>拆箱后的托管地址；保留 unbox 的判空与类型检查。</summary>
public sealed record UnboxAddressValue(ManagedValue Operand, TypeRef Target) : ManagedValue(new ByRefRef(Target), 64);
/// <summary>isinst：Operand 是 Target 类型（或其子类、实现）时为 Operand，否则为 null。</summary>
public sealed record IsInstValue(ManagedValue Operand, TypeRef Target, TypeRef? BoxedType = null) : ManagedValue(BoxedType ?? Target, 64);
public sealed record ArrayLengthValue(ManagedValue Array, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ArrayElementValue(ManagedValue Array, ManagedValue Index, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record FieldValue(ManagedValue Receiver, FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width)
{
    /// <summary>F9 认回证明；保留原字段的求值位置，避免把条件表达式里的调用提前执行。</summary>
    public FieldAccessor? Accessor { get; init; }
}
/// <summary>根或字段存储位置的托管地址；不把机器地址当整数。</summary>
public sealed record AddressValue(ManagedValue Target) : ManagedValue(new ByRefRef(Target.Type), 64);
/// <summary>固定数组并取得首元素地址；null 或空数组返回空指针。</summary>
public sealed record PinnedArrayValue(ManagedValue Array, ArrayRef ArrayType) : ManagedValue(new PointerRef(ArrayType.Element), 64);
/// <summary>非托管指针按字节偏移，不增加数组边界检查。</summary>
public sealed record PointerOffsetValue(ManagedValue Pointer, ManagedValue Offset) : ManagedValue(Pointer.Type, 64);
/// <summary>叶子均已证明的结构体值；L4 用 initobj 和逐叶子写入构造。</summary>
public sealed record ComposedValue(TypeRef StructType, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> Leaves) : ManagedValue(StructType, 0);
/// <summary>读取/写入已定型的结构体根，地址必须由托管存储位置证明。</summary>
public sealed record IndirectValue(ManagedValue Address, TypeRef Type, int Width = 0) : ManagedValue(Type, Width);
public sealed record StaticFieldValue(FieldRef Field, TypeRef Type, int Width) : ManagedValue(Type, Width)
{
    public FieldAccessor? Accessor { get; init; }
}
public sealed record BinaryValue(BinOp Op, ManagedValue Left, ManagedValue Right, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record UnaryValue(UnOp Op, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ConversionValue(ConvKind Kind, ManagedValue Operand, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record ComparisonValue(Cond Condition, ManagedValue Left, ManagedValue Right, TypeRef Type) : ManagedValue(Type, 1);
public sealed record ChoiceValue(ManagedValue Condition, ManagedValue True, ManagedValue False, TypeRef Type, int Width) : ManagedValue(Type, Width);
public sealed record BooleanValue(bool IsAnd, ManagedValue Left, ManagedValue Right, TypeRef Type) : ManagedValue(Type, 1);
public sealed record NegatedValue(ManagedValue Operand, TypeRef Type) : ManagedValue(Type, 1);
/// <summary>async 方法的返回（只出现在 <see cref="AsyncLifting"/> 提升出的方法体里）：以 Value（无结果时为 null）完成的任务，Type 是入口方法的返回类型。</summary>
public sealed record AsyncResultValue(ManagedValue? Value, TypeRef Type) : ManagedValue(Type, 0);
/// <summary>部分方法体中未恢复的值（只出现在 <see cref="MethodRecoveryResult.Partial"/> 里）。</summary>
public sealed record HoleValue(string Reason, TypeRef Type, int Width) : ManagedValue(Type, Width);

/// <summary>托管调用。Receiver 为 null 表示静态调用；Virtual 为真时按 callvirt 分派（并对接收者判空）。不含隐藏的 MethodInfo* 参数。</summary>
public sealed record ManagedInvocation(MethodRef Method, ManagedValue? Receiver, IReadOnlyList<ManagedValue> Arguments, bool Virtual);

public abstract record ManagedStatement(ulong Address);
public sealed record ManagedAssignment(ulong Address, LocalValue Target, ManagedValue Value) : ManagedStatement(Address);
/// <summary>写入字段、静态字段或数组元素。</summary>
public sealed record ManagedStore(ulong Address, ManagedValue Target, ManagedValue Value) : ManagedStatement(Address);
/// <summary>调用；Tail 为真时调用后立即以其结果返回。</summary>
public sealed record ManagedCall(ulong Address, ManagedInvocation Invocation, LocalValue? Result, bool Tail) : ManagedStatement(Address)
{
    /// <summary>由内联认回（<see cref="InlineRecognition"/>）得到：原生代码在此处内联了被调方法，执行对照按被调方法的方法体透明执行。</summary>
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
/// <summary>await Task（只出现在 <see cref="AsyncLifting"/> 提升出的 C# 输出方法体里）；Result 为 null 表示丢弃结果或无结果。</summary>
public sealed record ManagedAwait(ulong Address, ManagedValue Task, LocalValue? Result) : ManagedStatement(Address);
/// <summary>部分方法体中未恢复的语句；Terminal 为真时它结束所在的块（未恢复的终结语句）。</summary>
public sealed record ManagedHole(ulong Address, string Reason, bool Terminal) : ManagedStatement(Address);
/// <summary>Condition 成立时以无参构造函数 Exception 新建异常并抛出（L2 的判空、越界与 ThrowIf 未被后续访问吸收时）。</summary>
public sealed record ManagedCheck(ulong Address, ManagedValue Condition, MethodRef Exception) : ManagedStatement(Address);

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

/// <summary>未恢复之处：地址与原因。原因的第一个词用于分桶统计。</summary>
public sealed record RecoveryHole(ulong Address, string Reason, bool Derived = false);
public enum RuntimeDeclarationKind { Delegate, PlatformInvoke }
public sealed record MethodRecoveryResult(MethodRef Method, ulong Entry, ManagedBody? Body, IReadOnlyList<RecoveryHole> Holes)
{
    /// <summary>已核验的运行时声明；没有恢复原生方法体，不计入方法体及字节覆盖率。</summary>
    public RuntimeDeclarationKind? Declaration { get; init; }
    public NativeImport? PlatformImport { get; init; }
    /// <summary>有洞时已恢复部分组成的方法体：洞写成 <see cref="ManagedHole"/>/<see cref="HoleValue"/>，只供阅读，不进执行对照与指标。</summary>
    public ManagedBody? Partial { get; init; }
}

/// <summary>托管值的直接子项。</summary>
public static class ManagedValues
{
    public static IEnumerable<ManagedValue> Children(ManagedValue value) => value switch
    {
        FieldValue f => [f.Receiver],
        AddressValue a => [a.Target],
        PinnedArrayValue a => [a.Array], PointerOffsetValue p => [p.Pointer, p.Offset],
        IndirectValue i => [i.Address],
        ComposedValue c => c.Leaves.Select(l => l.Value),
        NewArrayValue a => [a.Length], ArrayLengthValue a => [a.Array], ArrayElementValue a => [a.Array, a.Index],
        BoxValue b => [b.Operand], UnboxAddressValue u => [u.Operand], IsInstValue i => [i.Operand], NewObjectValue n => n.Arguments,
        DelegateValue d => [d.Target],
        BinaryValue b => [b.Left, b.Right], UnaryValue u => [u.Operand], ConversionValue c => [c.Operand],
        ComparisonValue c => [c.Left, c.Right], ChoiceValue c => [c.Condition, c.True, c.False],
        BooleanValue b => [b.Left, b.Right], NegatedValue n => [n.Operand],
        AsyncResultValue r => r.Value is { } result ? [result] : [],
        ArgumentValue or LocalValue or ConstantValue or StringValue or TypeHandleValue or StaticFieldValue or HoleValue => [],
        _ => throw new NotSupportedException(value.ToString()),
    };

    /// <summary>
    /// 把 f 作用于直接子项并重建值（不递归、不改本层）。与 <see cref="Children"/> 是仅有的两处按值种类穷举的地方：
    /// 新增值种类时只改这两处，各改写器只处理自己关心的种类，其余交给这里。
    /// </summary>
    public static ManagedValue Map(ManagedValue value, Func<ManagedValue, ManagedValue> f) => value switch
    {
        FieldValue v => v with { Receiver = f(v.Receiver) },
        AddressValue v => v with { Target = f(v.Target) },
        PinnedArrayValue v => v with { Array = f(v.Array) },
        PointerOffsetValue v => v with { Pointer = f(v.Pointer), Offset = f(v.Offset) },
        IndirectValue v => v with { Address = f(v.Address) },
        ComposedValue v => v with { Leaves = v.Leaves.Select(l => (l.Path, f(l.Value))).ToArray() },
        NewArrayValue v => v with { Length = f(v.Length) },
        ArrayLengthValue v => v with { Array = f(v.Array) },
        ArrayElementValue v => v with { Array = f(v.Array), Index = f(v.Index) },
        BoxValue v => v with { Operand = f(v.Operand) },
        UnboxAddressValue v => v with { Operand = f(v.Operand) },
        IsInstValue v => v with { Operand = f(v.Operand) },
        NewObjectValue v => v with { Arguments = v.Arguments.Select(f).ToArray() },
        DelegateValue v => v with { Target = f(v.Target) },
        BinaryValue v => v with { Left = f(v.Left), Right = f(v.Right) },
        UnaryValue v => v with { Operand = f(v.Operand) },
        ConversionValue v => v with { Operand = f(v.Operand) },
        ComparisonValue v => v with { Left = f(v.Left), Right = f(v.Right) },
        ChoiceValue v => v with { Condition = f(v.Condition), True = f(v.True), False = f(v.False) },
        BooleanValue v => v with { Left = f(v.Left), Right = f(v.Right) },
        NegatedValue v => v with { Operand = f(v.Operand) },
        AsyncResultValue v => v with { Value = v.Value is { } result ? f(result) : null },
        ArgumentValue or LocalValue or ConstantValue or StringValue or TypeHandleValue or StaticFieldValue or HoleValue => value,
        _ => throw new NotSupportedException(value.ToString()),
    };

    public static IEnumerable<ManagedValue> Walk(ManagedValue value) =>
        Children(value).SelectMany(Walk).Prepend(value);

    public static IEnumerable<ManagedValue> Of(ManagedInvocation invocation) =>
        invocation.Receiver is { } receiver ? invocation.Arguments.Prepend(receiver) : invocation.Arguments;

    /// <summary>
    /// 语句级的 <see cref="Map"/>：把 value 作用于语句直接包含的值（含边上的并行复制），存储的目标改用 target（默认同 value）。
    /// 赋值的目标是局部变量，不改。与 <see cref="Of(ManagedStatement)"/> 是仅有的两处按语句种类穷举的遍历。
    /// </summary>
    public static ManagedStatement Map(ManagedStatement statement, Func<ManagedValue, ManagedValue> value, Func<ManagedValue, ManagedValue>? target = null)
    {
        target ??= value;
        ManagedEdge Edge(ManagedEdge edge) => edge with { Copies = edge.Copies.Select(c => c with { Value = value(c.Value) }).ToArray() };
        return statement switch
        {
            ManagedAssignment a => a with { Value = value(a.Value) },
            ManagedStore s => s with { Target = target(s.Target), Value = value(s.Value) },
            ManagedCall c => c with { Invocation = c.Invocation with
            {
                Receiver = c.Invocation.Receiver is { } receiver ? value(receiver) : null,
                Arguments = c.Invocation.Arguments.Select(value).ToArray(),
            } },
            ManagedReturn r => r with { Value = r.Value is { } returned ? value(returned) : null },
            ManagedJump j => j with { Edge = Edge(j.Edge) },
            ManagedBranch b => b with { Condition = value(b.Condition), Taken = Edge(b.Taken), Fallthrough = Edge(b.Fallthrough) },
            ManagedSwitch w => w with { Index = value(w.Index), Cases = w.Cases.Select(Edge).ToArray() },
            ManagedThrow t => t with { Exception = value(t.Exception) },
            ManagedCheck c => c with { Condition = value(c.Condition) },
            ManagedAwait a => a with { Task = value(a.Task) },
            ManagedRethrow or ManagedEndFault or ManagedHole => statement,
            _ => throw new NotSupportedException(statement.ToString()),
        };
    }

    /// <summary>对方法体的每条语句做 <see cref="Map(ManagedStatement, Func{ManagedValue, ManagedValue}, Func{ManagedValue, ManagedValue}?)"/>。</summary>
    public static ManagedBody Map(ManagedBody body, Func<ManagedValue, ManagedValue> value, Func<ManagedValue, ManagedValue>? target = null) =>
        body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(s => Map(s, value, target)).ToArray() }).ToArray() };

    /// <summary>语句的出边（跳转、分支、switch）；其余语句为空。按语句种类列出出边的唯一地方。</summary>
    public static IReadOnlyList<ManagedEdge> Edges(ManagedStatement statement) => statement switch
    {
        ManagedJump j => [j.Edge],
        ManagedBranch b => [b.Taken, b.Fallthrough],
        ManagedSwitch w => w.Cases,
        _ => [],
    };

    /// <summary>改写语句的出边（目标与边上的复制）。</summary>
    public static ManagedStatement MapEdges(ManagedStatement statement, Func<ManagedEdge, ManagedEdge> edge) => statement switch
    {
        ManagedJump j => j with { Edge = edge(j.Edge) },
        ManagedBranch b => b with { Taken = edge(b.Taken), Fallthrough = edge(b.Fallthrough) },
        ManagedSwitch w => w with { Cases = w.Cases.Select(edge).ToArray() },
        _ => statement,
    };

    /// <summary>出边上复制的源值。</summary>
    public static IEnumerable<ManagedValue> CopiedValues(ManagedStatement statement) => Edges(statement).SelectMany(e => e.Copies).Select(c => c.Value);

    /// <summary>语句直接包含的值（不含边赋值）。</summary>
    public static IEnumerable<ManagedValue> Of(ManagedStatement statement) => statement switch
    {
        ManagedAssignment a => [a.Target, a.Value],
        ManagedStore s => [s.Target, s.Value],
        ManagedCall c => Of(c.Invocation),
        ManagedReturn r => r.Value is { } v ? [v] : [],
        ManagedBranch b => [b.Condition],
        ManagedSwitch w => [w.Index],
        ManagedThrow t => [t.Exception],
        ManagedCheck c => [c.Condition],
        ManagedAwait a => [a.Task],
        ManagedJump or ManagedRethrow or ManagedEndFault or ManagedHole => [],
        _ => throw new NotSupportedException(statement.ToString()),
    };
}
