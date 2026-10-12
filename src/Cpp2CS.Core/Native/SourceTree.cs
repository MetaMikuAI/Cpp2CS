namespace Cpp2CS.Native;

// 源码投影的结构化遍历；不通过文本替换变量或成员。
public static class SourceTree
{
    public static Expression Map(Expression e, Func<Expression, Expression> rewrite) => rewrite(e switch
    {
        CapturedExpression c => c with { Value = Map(c.Value, rewrite) },
        IndexedArrayAddress a => a with { Array = Map(a.Array, rewrite), Index = Map(a.Index, rewrite) },
        MemberExpression m => m with { Receiver = Map(m.Receiver, rewrite) },
        AddressOfExpression a => a with { Target = Map(a.Target, rewrite) },
        BinaryExpression b => b with { Left = Map(b.Left, rewrite), Right = Map(b.Right, rewrite) },
        SliceExpression s => s with { Value = Map(s.Value, rewrite) },
        ComposeExpression c => c with { Parts = c.Parts.Select(p => Map(p, rewrite)).ToArray() },
        AggregateExpression a => a with { Bits = Map(a.Bits, rewrite) },
        OperationExpression o => o with { Arguments = o.Arguments.Select(p => Map(p, rewrite)).ToArray() },
        InvocationExpression c => c with { Receiver = c.Receiver is null ? null : Map(c.Receiver, rewrite), Arguments = c.Arguments.Select(p => Map(p, rewrite)).ToArray() },
        LambdaExpression l => l with { Body = Map(l.Body, rewrite) },
        LambdaBlockExpression b => b with { Body = Map(b.Body, rewrite) },
        _ => e
    });
    public static Statement Map(Statement s, Func<Expression, Expression> rewrite) => s switch
    {
        AssignStatement a => a with { Value = Map(a.Value, rewrite) },
        SetLocalStatement a => a with { Value = Map(a.Value, rewrite) },
        CallStatement c => c with { Receiver = c.Receiver is null ? null : Map(c.Receiver, rewrite), Arguments = c.Arguments.Select(p => Map(p, rewrite)).ToArray() },
        StoreStatement w => w with { Target = Map(w.Target, rewrite), Value = Map(w.Value, rewrite) },
        ReturnStatement r => r with { Value = r.Value is null ? null : Map(r.Value, rewrite) },
        ConditionalInvokeStatement c => c with { Receiver = Map(c.Receiver, rewrite), Arguments = c.Arguments.Select(p => Map(p, rewrite)).ToArray() },
        _ => s
    };
    public static LiftResult Map(LiftResult source, Func<Expression, Expression> rewrite) => source with
    {
        Blocks = source.Blocks.ToDictionary(p => p.Key, p => p.Value with
        { Statements = p.Value.Statements.Select(s => Map(s, rewrite)).ToList(), Condition = p.Value.Condition is null ? null : Map(p.Value.Condition, rewrite) }),
        Proofs = [.. source.Proofs]
    };
}
