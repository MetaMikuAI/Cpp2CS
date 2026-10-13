namespace Cpp2CS.Native;

public static class SemanticData
{
    public static object Expression(Expression expression) => expression switch
    {
        NameExpression n => new { kind = "name", n.Name },
        IndexedArrayAddress a => new { kind = "unresolved-array-address", array = Expression(a.Array), index = Expression(a.Index) },
        StaticMemberExpression m => new { kind = "static-member", m.Owner, m.Name, m.Type, m.IsProperty },
        CapturedExpression c => new { kind = "capture", c.Name },
        ConstantExpression c => new { kind = "constant", c.Value, c.EnumType, c.EnumMember },
        OperationExpression o => new { kind = "operation", operation = o.Operation.ToString(), o.Type, arguments = o.Arguments.Select(Expression).ToArray() },
        AddressExpression a => new { kind = "global", a.Address },
        AddressOfExpression a => new { kind = "address-of", target = Expression(a.Target), rootType = a.RootType },
        StackAddressExpression a => new { kind = "stack-address", a.Offset },
        MetadataExpression m => new { kind = "metadata", m.IsSlot, m.Reference.Slot, m.Reference.Name },
        MemberExpression m => new { kind = "member", receiver = Expression(m.Receiver), m.Field.Offset, m.Field.Size, m.Field.Name },
        SourceMemberExpression m => new { kind = "source-member", receiver = Expression(m.Receiver), m.Name, m.Type },
        AwaitExpression a => new { kind = "await", value = Expression(a.Value) },
        CastExpression c => new { kind = "cast", c.Type, value = Expression(c.Value) },
        ObjectValueExpression o => new { kind = "object-value", o.Type, fields = o.Fields.Select(f => new { f.Name, value = Expression(f.Value) }) },
        BinaryExpression b => new { kind = "binary", b.Operator, left = Expression(b.Left), right = Expression(b.Right) },
        SliceExpression s => new { kind = "slice", value = Expression(s.Value), s.BitOffset, s.BitWidth },
        ComposeExpression c => new { kind = "compose", parts = c.Parts.Select(Expression).ToArray(), c.BitWidths },
        AggregateExpression a => new { kind = "aggregate", a.Type, bits = Expression(a.Bits) },
        InvocationExpression c => new { kind = "invocation", c.Name, c.IsProperty, receiver = c.Receiver is null ? null : Expression(c.Receiver), arguments = c.Arguments.Select(Expression).ToArray() },
        LambdaExpression l => new { kind = "lambda", l.Parameters, l.MethodAddress, body = Expression(l.Body) },
        LambdaBlockExpression b => new { kind = "lambda-block", body = Function(b.Body) },
        UnknownExpression u => new { kind = "unknown", u.Reason },
        _ => throw new InvalidOperationException("未序列化的表达式")
    };
    public static object Statement(Statement statement) => statement switch
    {
        AssignStatement a => new { kind = "assign", a.Address, a.Name, a.Type, value = Expression(a.Value) },
        EvaluateStatement e => new { kind = "evaluate", e.Address, value = Expression(e.Value) },
        DeclareStatement d => new { kind = "declare", d.Address, d.Name, d.Type },
        SetLocalStatement s => new { kind = "set-local", s.Address, s.Name, value = Expression(s.Value) },
        CallStatement c => new { kind = "call", c.Address, c.Name, c.Result, c.IsInstance, c.NoReturn, c.DeclaringType, receiver = c.Receiver is null ? null : Expression(c.Receiver), arguments = c.Arguments.Select(Expression).ToArray() },
        StoreStatement s => new { kind = "store", s.Address, target = Expression(s.Target), value = Expression(s.Value) },
        ThrowStatement t => new { kind = "throw", t.Address, t.Type },
        ReturnStatement r => new { kind = "return", r.Address, value = r.Value is null ? null : Expression(r.Value) },
        UnresolvedStatement u => new { kind = "unknown", u.Address, u.Reason },
        EnsureMetadataStatement m => new { kind = "ensure-metadata", m.Address, m.Flag, slots = m.References.Select(r => r.Slot).ToArray() },
        ConditionalInvokeStatement c => new { kind = "conditional-invoke", c.Address, receiver = Expression(c.Receiver), arguments = c.Arguments.Select(Expression).ToArray() },
        DelegateCacheStatement c => new { kind = "delegate-cache", c.Address, c.Name, c.Type, cache = Expression(c.Cache), target = Expression(c.Target), method = Expression(c.Method) },
        _ => throw new InvalidOperationException("未序列化的语句")
    };
    public static object Function(LiftResult result) => new
    {
        entry = result.Method.Address,
        sourceProjection = result.IsSourceProjection,
        blocks = result.Blocks.Values.Select(b => new
        {
            b.Address, b.Successors,
            condition = b.Condition is null ? null : Expression(b.Condition),
            statements = b.Statements.Select(Statement)
        })
    };
}
