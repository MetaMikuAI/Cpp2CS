using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

public static partial class AsyncLifting
{
    private sealed partial class Lifter
    {
        // UniTask<T> 的两条 GetResult 路径：有 source 时调用它，否则直接读取 task.result。
        // 比较结果代入后的分支与边复制，保留有 source 的路径，把调用替换成 await。
        private bool FoldInlineResult(LocalValue held, ManagedBranch guard, List<ManagedStatement> guardStatements,
            ManagedEdge empty, ManagedEdge present, Dictionary<Variable, ManagedValue> definitions,
            Func<ManagedValue, string, bool> member, Func<ManagedCall, bool> sourceCall, Func<ulong, ulong> skipJumps)
        {
            if (held.Type is not DefinitionRef { Arguments.Count: 1 }) return false;
            List<ulong> Path(ulong start)
            {
                var path = new List<ulong>();
                var seen = new HashSet<ulong>();
                while (seen.Add(start))
                {
                    path.Add(start);
                    if (blocks[start].LastOrDefault() is not ManagedJump { Edge.Copies.Count: 0 } jump) break;
                    start = jump.Edge.Target;
                }
                return path;
            }
            var emptyPath = Path(empty.Target);
            var presentPath = Path(present.Target);
            var common = emptyPath.Intersect(presentPath).ToHashSet();
            var calls = presentPath.TakeWhile(a => !common.Contains(a)).SelectMany(a => blocks[a]).OfType<ManagedCall>()
                .Where(c => c.Invocation.Method.Method.Name == "GetResult" && c.Result is not null && sourceCall(c)).ToArray();
            if (calls is not [var call]) return false;
            var result = call.Result!;
            ManagedValue Canonical(ManagedValue value, HashSet<Variable> seen)
            {
                if (value is LocalValue local && local.Variable != result.Variable && seen.Add(local.Variable)
                    && definitions.TryGetValue(local.Variable, out var definition))
                    return Canonical(definition, seen);
                if (StorageValue(value) is FieldValue field && member(field, "result")) return result;
                var mapped = ManagedValues.Map(value, child => Canonical(child, new(seen)));
                // C# bool 已是 0/1；ARM64 的 AND 1 与整数扩展不改变其真假。
                static bool Bool(ManagedValue v) => v.Type is DefinitionRef { Definition.Keyword: "bool" };
                return mapped switch
                {
                    ConversionValue
                    {
                        Kind: ConvKind.Truncate, Operand: ConversionValue
                        { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: var narrow }
                    } conversion
                        when conversion.Width == narrow.Width => narrow,
                    ComparisonValue { Condition: Cond.Eq or Cond.Ne, Left: var operand, Right: ConstantValue constant } comparison
                        when operand.Type is DefinitionRef { Definition.IsEnum: true } && constant.Width == operand.Width
                        => comparison with { Right = new ConstantValue(constant.Bits, operand.Type, operand.Width) },
                    ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: var operand } when Bool(operand) => operand,
                    BinaryValue { Op: BinOp.And, Left: var left, Right: ConstantValue { Bits: 1 } } when Bool(left) => left,
                    ComparisonValue { Condition: Cond.Ne, Left: var left, Right: ConstantValue { Bits: 0 } } when Bool(left) => left,
                    ComparisonValue { Condition: Cond.Eq, Left: var left, Right: ConstantValue { Bits: 0 }, Type: var type } when Bool(left) => new NegatedValue(left, type),
                    // cset/csel 可把同一 bool 写成条件选择 0/1；仅用于比较两条结果路径。
                    ChoiceValue { Condition: var condition, True: ConstantValue { Bits: 1 }, False: ConstantValue { Bits: 0 } } when Bool(condition) => condition,
                    ChoiceValue { Condition: NegatedValue { Operand: var operand }, True: ConstantValue { Bits: 0 }, False: ConstantValue { Bits: 1 } } when Bool(operand) => operand,
                    ChoiceValue { Condition: var condition, True: ConstantValue { Bits: 0 }, False: ConstantValue { Bits: 1 } } when Bool(condition) => new NegatedValue(condition, condition.Type),
                    _ => mapped,
                };
            }
            ManagedValue Value(ManagedValue value) => Canonical(value, []);
            bool ResultRead(ManagedValue value) => ManagedValues.Walk(value).OfType<FieldValue>().Any(f => member(f, "result"));
            bool ProtocolRead(ManagedValue value) => member(value, "source") || member(value, "token");
            bool PureResult(ManagedValue value) => ManagedValues.Walk(Value(value)).All(v => v is ConstantValue or ConversionValue or ComparisonValue
                or NegatedValue or BooleanValue or FieldValue or AddressValue or IndirectValue
                or BinaryValue { Op: not (BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem) }
                || v is LocalValue local && local.Variable == result.Variable);
            var readResult = false;
            var emptyLocals = new HashSet<Variable>();
            ManagedStatement? Continuation(List<ulong> path, bool isEmpty)
            {
                foreach (var address in path)
                {
                    if (common.Contains(address)) return new ManagedJump(0, new(address, []));
                    foreach (var statement in blocks[address])
                    {
                        if (statement == call && !isEmpty) continue;
                        if (statement is ManagedAssignment assignment && (ProtocolRead(assignment.Value) || PureResult(assignment.Value)))
                        {
                            if (isEmpty) { emptyLocals.Add(assignment.Target.Variable); readResult |= ResultRead(assignment.Value); }
                            continue;
                        }
                        if (statement is ManagedJump { Edge.Copies.Count: 0 } jump && !common.Contains(jump.Edge.Target)) continue;
                        if (statement is ManagedJump or ManagedBranch)
                        {
                            if (isEmpty) readResult |= ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Any(ResultRead);
                            return ManagedValues.Map(statement, Value);
                        }
                        return null;
                    }
                }
                return null;
            }
            var left = Continuation(emptyPath, true);
            var right = Continuation(presentPath, false);
            bool Edge(ManagedEdge a, ManagedEdge b) => skipJumps(a.Target) == skipJumps(b.Target)
                && a.Copies.Count == b.Copies.Count && a.Copies.Zip(b.Copies).All(p => p.First.Target == p.Second.Target && p.First.Value == p.Second.Value);
            static bool Opposite(ManagedValue a, ManagedValue b) => a is NegatedValue n && n.Operand == b
                || b is NegatedValue m && m.Operand == a
                || a is ComparisonValue { Condition: Cond.Eq or Cond.Ne } x && b is ComparisonValue { Condition: Cond.Eq or Cond.Ne } y
                    && x.Condition != y.Condition && x.Left == y.Left && x.Right == y.Right;
            var equivalent = (left, right) switch
            {
                (ManagedJump a, ManagedJump b) => Edge(a.Edge, b.Edge),
                (ManagedBranch a, ManagedBranch b) => a.Condition == b.Condition && Edge(a.Taken, b.Taken) && Edge(a.Fallthrough, b.Fallthrough),
                _ => false,
            };
            if (left is ManagedBranch first && right is ManagedBranch second && Opposite(first.Condition, second.Condition))
                equivalent = Edge(first.Taken, second.Fallthrough) && Edge(first.Fallthrough, second.Taken);
            var unusedResult = !blocks.Values.SelectMany(s => s).SelectMany(s =>
                    (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => l.Variable == result.Variable);
            if (!equivalent || !readResult && !unusedResult) return false;
            // 空 source 分支的临时结果必须通过已核对的边复制传出，不能有分支外的隐式使用。
            var removed = emptyPath.TakeWhile(a => !common.Contains(a)).ToHashSet();
            if (order.Where(a => !removed.Contains(a)).SelectMany(a => blocks[a]).SelectMany(s =>
                ManagedValues.Of(s).Where(v => s is not ManagedAssignment a || v != a.Target).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => emptyLocals.Contains(l.Variable))) return false;
            guardStatements[^1] = new ManagedJump(guard.Address, present);
            var statements = blocks[presentPath.Single(a => blocks[a].Contains(call))];
            statements[statements.IndexOf(call)] = new ManagedAwait(call.Address, held, unusedResult ? null : result);
            return true;
        }
    }
}
