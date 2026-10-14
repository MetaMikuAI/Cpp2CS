namespace Cpp2CS.Native;

public static class SemanticValidation
{
    // 路径收缩后，快照仍须在所有到达使用点的路径上先完成读取。
    public static void CheckReadSnapshots(LiftResult result, IReadOnlySet<string> names)
    {
        if (names.Count == 0) return;
        var reachable = new HashSet<ulong>(); var pending = new Stack<ulong>(); pending.Push(result.Method.Address);
        while (pending.TryPop(out var pc))
            if (reachable.Add(pc)) foreach (var next in result.Blocks[pc].Successors) pending.Push(next);
        var predecessors = reachable.ToDictionary(pc => pc, pc => reachable.Where(p => result.Blocks[p].Successors.Contains(pc)).ToArray());
        var assigned = reachable.ToDictionary(pc => pc, pc => result.Blocks[pc].Statements.OfType<AssignStatement>().Select(s => s.Name).Where(names.Contains).ToHashSet());
        var available = reachable.ToDictionary(pc => pc, _ => names.ToHashSet());
        HashSet<string> Incoming(ulong pc)
        {
            if (pc == result.Method.Address || predecessors[pc].Length == 0) return [];
            var known = available[predecessors[pc][0]].ToHashSet();
            foreach (var predecessor in predecessors[pc].Skip(1)) known.IntersectWith(available[predecessor]);
            return known;
        }
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var pc in reachable)
            {
                var next = Incoming(pc); next.UnionWith(assigned[pc]);
                if (!next.SetEquals(available[pc])) { available[pc] = next; changed = true; }
            }
        }
        foreach (var pc in reachable)
        {
            var known = Incoming(pc);
            Expression Inspect(Expression value)
            {
                if (value is NameExpression name && names.Contains(name.Name) && !known.Contains(name.Name))
                {
                    var problem = $"0x{pc:x}: 字段快照未在所有路径定义：{name.Name}";
                    if (!result.Problems.Contains(problem)) result.Problems.Add(problem);
                }
                return value;
            }
            foreach (var statement in result.Blocks[pc].Statements)
            {
                SourceTree.Map(statement, Inspect);
                if (statement is AssignStatement assignment && names.Contains(assignment.Name)) known.Add(assignment.Name);
            }
            if (result.Blocks[pc].Condition is { } condition) SourceTree.Map(condition, Inspect);
        }
    }
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
                    EvaluateStatement e => [e.Value],
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
                case PhiExpression phi:
                    var unresolved = $"0x{pc:x}: Phi 尚未按前驱降低：{phi.Name}";
                    if (!result.Problems.Contains(unresolved)) result.Problems.Add(unresolved);
                    foreach (var input in phi.Inputs) Inspect(pc, input.Value);
                    break;
                case IndexedArrayAddress:
                    result.Problems.Add($"0x{pc:x}: 数组地址尚未绑定到元素读取"); break;
                case ParameterAddressExpression:
                    result.Problems.Add($"0x{pc:x}: 参数存储地址尚未投影为值或明确的引用传递"); break;
                case UnknownExpression unknown:
                    var problem = $"0x{pc:x}: 语义输入未确定: {unknown.Reason}";
                    if (!result.Problems.Contains(problem)) result.Problems.Add(problem);
                    break;
                case CapturedExpression captured: Inspect(pc, captured.Value); break;
                case MemberExpression member: Inspect(pc, member.Receiver); break;
                case SourceMemberExpression member: Inspect(pc, member.Receiver); break;
                case AwaitExpression awaited: Inspect(pc, awaited.Value); break;
                case CastExpression cast: Inspect(pc, cast.Value); break;
                case ObjectValueExpression obj: foreach (var field in obj.Fields) Inspect(pc, field.Value); break;
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
