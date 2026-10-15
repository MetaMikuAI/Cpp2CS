namespace Cpp2CS.Managed;

/// <summary>托管值的直接子项与语句中的全部值，包括写入位置和边赋值。</summary>
public static class ValueTree
{
    public static IEnumerable<ManagedValue> Children(ManagedValue value) => value switch
    {
        AddressValue a => [a.Target], AggregateValue a => a.Members.Select(m => m.Value),
        FieldValue f => [f.Receiver], IndirectValue i => [i.Address],
        InvocationValue i => i.Invocation.Receiver is { } receiver ? new[] { receiver }.Concat(i.Invocation.Arguments) : i.Invocation.Arguments,
        NewArrayValue a => [a.Length], ArrayLengthValue a => [a.Array], ArrayElementValue a => [a.Array, a.Index],
        BoxValue b => [b.Operand], NewObjectValue n => n.Arguments,
        BinaryValue b => [b.Left, b.Right], UnaryValue u => [u.Operand], ConversionValue c => [c.Operand],
        ComparisonValue c => [c.Left, c.Right], ChoiceValue c => [c.Condition, c.True, c.False],
        BooleanValue b => [b.Left, b.Right], NegatedValue n => [n.Operand],
        ArgumentValue or LocalValue or StackLocalValue or DefaultValue or ConstantValue or StringValue or TypeHandleValue or StaticFieldValue or ObjectAllocationValue => [],
        _ => throw new NotSupportedException(value.ToString()),
    };

    public static IEnumerable<ManagedValue> Walk(ManagedValue value)
    {
        yield return value;
        foreach (var child in Children(value))
            foreach (var item in Walk(child)) yield return item;
    }

    public static IEnumerable<ManagedValue> Values(ManagedStatement statement) => statement switch
    {
        ManagedAssignment a => [a.Target, a.Value], ManagedStore s => [s.Target, s.Value],
        ManagedCall c => (c.Invocation.Receiver is { } receiver ? new[] { receiver } : []).Concat(c.Invocation.Arguments)
            .Concat(c.Result is { } result ? [result] : []),
        ManagedReturn r => r.Value is { } value ? [value] : [],
        ManagedJump j => j.Edge.Copies.SelectMany(c => new ManagedValue[] { c.Target, c.Value }),
        ManagedBranch b => new[] { b.Condition }.Concat(b.Taken.Copies.Concat(b.Fallthrough.Copies).SelectMany(c => new ManagedValue[] { c.Target, c.Value })),
        _ => throw new NotSupportedException(statement.ToString()),
    };
}
