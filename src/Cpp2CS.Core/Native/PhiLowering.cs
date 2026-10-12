namespace Cpp2CS.Native;

// 无环图中只展开被使用的 Phi；在对应前驱赋值，避免把不同路径的寄存器值混合。
public static class PhiLowering
{
    public static void Apply(LiftResult result)
    {
        var live = new Dictionary<string, PhiExpression>();
        Expression Rewrite(Expression e) => e switch
        {
            PhiExpression phi => Reference(phi),
            CapturedExpression c => c with { Value = Rewrite(c.Value) },
            MemberExpression m => m with { Receiver = Rewrite(m.Receiver) },
            AddressOfExpression a => a with { Target = Rewrite(a.Target) },
            SliceExpression s => s with { Value = Rewrite(s.Value) },
            ComposeExpression c => c with { Parts = c.Parts.Select(Rewrite).ToArray() },
            AggregateExpression a => a with { Bits = Rewrite(a.Bits) },
            BinaryExpression b => b with { Left = Rewrite(b.Left), Right = Rewrite(b.Right) },
            OperationExpression o => o with { Arguments = o.Arguments.Select(Rewrite).ToArray() },
            InvocationExpression c => c with { Receiver = c.Receiver is null ? null : Rewrite(c.Receiver), Arguments = c.Arguments.Select(Rewrite).ToArray() },
            _ => e
        };
        Expression Reference(PhiExpression phi)
        {
            if (!live.ContainsKey(phi.Name))
            {
                live.Add(phi.Name, phi);
                foreach (var input in phi.Inputs) Rewrite(input.Value);
            }
            return new NameExpression(phi.Name);
        }
        foreach (var block in result.Blocks.Values.ToArray())
        {
            var statements = block.Statements.Select(s => s switch
            {
                AssignStatement a => a with { Value = Rewrite(a.Value) },
                StoreStatement w => w with { Target = Rewrite(w.Target), Value = Rewrite(w.Value) },
                CallStatement c => c with { Receiver = c.Receiver is null ? null : Rewrite(c.Receiver), Arguments = c.Arguments.Select(Rewrite).ToArray() },
                ReturnStatement r => r with { Value = r.Value is null ? null : Rewrite(r.Value) },
                _ => s
            }).ToList();
            result.Blocks[block.Address] = block with { Statements = statements, Condition = block.Condition is null ? null : Rewrite(block.Condition) };
        }
        foreach (var phi in live.Values)
        {
            if (phi.Type == "unknown") result.Problems.Add("Phi 类型未确定：" + phi.Name);
            result.Blocks[result.Method.Address].Statements.Insert(0, new DeclareStatement(result.Method.Address, phi.Name, phi.Type));
            foreach (var input in phi.Inputs)
                result.Blocks[input.Predecessor].Statements.Add(new SetLocalStatement(input.Predecessor, phi.Name, Rewrite(input.Value)));
        }
        if (live.Count > 0) result.Proofs.Add(new(result.Method.Address, "PredecessorPhi", $"{live.Count} live acyclic Phi values; assignments retain predecessor identity; dead register joins not emitted"));
    }
}
