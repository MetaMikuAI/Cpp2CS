
namespace Cpp2CS.Managed;

/// <summary>托管值的直接子项。</summary>
public static class ManagedValues
{
    public static IEnumerable<ManagedValue> Children(ManagedValue value) => value switch
    {
        FieldValue f => [f.Receiver],
        AddressValue a => [a.Target],
        PinnedArrayValue a => [a.Array],
        PointerOffsetValue p => [p.Pointer, p.Offset],
        IndirectValue i => [i.Address],
        ComposedValue c => c.Leaves.Select(l => l.Value),
        NewArrayValue a => [a.Length],
        ArrayLengthValue a => [a.Array],
        ArrayElementValue a => [a.Array, a.Index],
        BoxValue b => [b.Operand],
        UnboxAddressValue u => [u.Operand],
        UnboxValue u => [u.Operand],
        IsInstValue i => [i.Operand],
        CheckedCastValue c => [c.Operand],
        NewObjectValue n => n.Arguments,
        DelegateValue d => [d.Target],
        BinaryValue b => [b.Left, b.Right],
        UnaryValue u => [u.Operand],
        ConversionValue c => [c.Operand],
        ComparisonValue c => [c.Left, c.Right],
        ChoiceValue c => [c.Condition, c.True, c.False],
        BooleanValue b => [b.Left, b.Right],
        NegatedValue n => [n.Operand],
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
        UnboxValue v => v with { Operand = f(v.Operand) },
        IsInstValue v => v with { Operand = f(v.Operand) },
        CheckedCastValue v => v with { Operand = f(v.Operand) },
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
            ManagedCall c => c with
            {
                Invocation = c.Invocation with
                {
                    Receiver = c.Invocation.Receiver is { } receiver ? value(receiver) : null,
                    Arguments = c.Invocation.Arguments.Select(value).ToArray(),
                }
            },
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
