namespace Cpp2CS.Native;

public static class SemanticValidation
{
    public static void Check(LiftResult result)
    {
        foreach (var block in result.Blocks.Values)
        {
            Inspect(block.Address, block.Condition);
            foreach (var statement in block.Statements)
            {
                Expression?[] values = statement switch
                {
                    CallStatement c => [c.Receiver, .. c.Arguments],
                    ConditionalInvokeStatement c => [c.Receiver, .. c.Arguments],
                    AssignStatement a => [a.Value],
                    SetLocalStatement s => [s.Value],
                    StoreStatement s => [s.Target, s.Value],
                    ReturnStatement r => [r.Value],
                    _ => []
                };
                foreach (var value in values) Inspect(statement.Address, value);
            }
        }
        void Inspect(ulong pc, Expression? value)
        {
            switch (value)
            {
                case IndexedArrayAddress:
                    result.Problems.Add($"0x{pc:x}: 数组地址尚未绑定到元素读取"); break;
                case UnknownExpression unknown:
                    var problem = $"0x{pc:x}: 语义输入未确定: {unknown.Reason}";
                    if (!result.Problems.Contains(problem)) result.Problems.Add(problem);
                    break;
                case CapturedExpression captured: Inspect(pc, captured.Value); break;
                case MemberExpression member: Inspect(pc, member.Receiver); break;
                case AddressOfExpression address: Inspect(pc, address.Target); break;
                case SliceExpression slice: Inspect(pc, slice.Value); break;
                case ComposeExpression compose: foreach (var part in compose.Parts) Inspect(pc, part); break;
                case AggregateExpression aggregate: Inspect(pc, aggregate.Bits); break;
                case BinaryExpression binary: Inspect(pc, binary.Left); Inspect(pc, binary.Right); break;
                case OperationExpression operation: foreach (var argument in operation.Arguments) Inspect(pc, argument); break;
                case InvocationExpression invocation: Inspect(pc, invocation.Receiver); foreach (var argument in invocation.Arguments) Inspect(pc, argument); break;
            }
        }
    }
}
