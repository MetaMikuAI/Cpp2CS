namespace Cpp2CS.Native;

// 无环图中只展开被使用的 Phi；在对应前驱赋值，避免把不同路径的寄存器值混合。
public static class PhiLowering
{
    public static void Apply(LiftResult result)
    {
        var live = new Dictionary<string, PhiExpression>();
        Expression ReferenceNode(Expression e) => e is PhiExpression phi ? Reference(phi) : e;
        Expression Rewrite(Expression e) => SourceTree.Map(e, ReferenceNode);
        Expression Reference(PhiExpression phi)
        {
            live.TryAdd(phi.Name, phi);
            return new NameExpression(phi.Name);
        }
        foreach (var block in result.Blocks.Values.ToArray())
        {
            var statements = block.Statements.Select(s => SourceTree.Map(s, ReferenceNode)).ToList();
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
