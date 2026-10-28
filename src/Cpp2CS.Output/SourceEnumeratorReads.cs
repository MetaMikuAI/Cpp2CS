using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Cpp2CS.Ir;

namespace Cpp2CS.Output;

/// <summary>局部值类型枚举器的原生字段读取可提前越过纯读取，保留调用、写入和异常区域边界。</summary>
internal static class SourceEnumeratorReads
{
    internal static ManagedBody Rewrite(ManagedBody body, Func<FieldValue, bool> currentField, Func<FieldValue, LocalValue>? snapshot = null)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address, b => b.Statements.ToList());
        var incoming = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (e.Target, Block: b.Address)))
            .GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Select(e => e.Block).ToArray());
        var handlers = body.Regions.Select(r => r.HandlerEntry).ToHashSet();
        var handlerBlocks = body.Regions.SelectMany(r => r.Handler).ToHashSet();
        var handlerLocals = body.Blocks.Where(b => handlerBlocks.Contains(b.Address)).SelectMany(b => b.Statements)
            .SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(v => v.Variable).ToHashSet();
        var calls = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable).ToHashSet();
        var assignments = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable)
            .ToDictionary(g => g.Key, g => g.Select(a => a.Value).ToArray());
        bool CallResult(ManagedValue value, HashSet<Variable> seen) => ManagedValues.Walk(value).OfType<LocalValue>().Any(local =>
            calls.Contains(local.Variable) || seen.Add(local.Variable) && assignments.TryGetValue(local.Variable, out var values) && values.Any(v => CallResult(v, seen)));
        bool SameRegion(ulong a, ulong b) => body.Regions.All(r => r.Try.Contains(a) == r.Try.Contains(b) && r.Handler.Contains(a) == r.Handler.Contains(b));
        static bool ReadOnly(ManagedValue value) => value switch
        {
            LocalValue or ArgumentValue or ConstantValue => true,
            FieldValue { Accessor: null } field => ReadOnly(field.Receiver),
            ArrayLengthValue length => ReadOnly(length.Array),
            ConversionValue conversion => ReadOnly(conversion.Operand),
            BinaryValue binary => ReadOnly(binary.Left) && ReadOnly(binary.Right),
            ComparisonValue comparison => ReadOnly(comparison.Left) && ReadOnly(comparison.Right),
            NegatedValue negated => ReadOnly(negated.Operand),
            _ => false,
        };
        foreach (var source in body.Blocks)
        foreach (var read in source.Statements.OfType<ManagedAssignment>())
        {
            if (read.Value is not FieldValue { Receiver: AddressValue { Target: LocalValue local } } field
                || local.Type is not DefinitionRef { Definition.IsValueType: true } || handlerLocals.Contains(read.Target.Variable)
                || !currentField(field)) continue;
            var sourceIndex = blocks[source.Address].IndexOf(read);
            var destination = source.Address;
            var index = sourceIndex;
            var visited = new HashSet<ulong> { destination };
            var crossed = false;
            var branched = false;
            while (true)
            {
                if (index > 0)
                {
                    if (blocks[destination][index - 1] is ManagedCheck check && ReadOnly(check.Condition)
                        && !ManagedValues.Walk(check.Condition).OfType<LocalValue>().Any(v => v.Variable == read.Target.Variable))
                    { index--; crossed = true; continue; }
                    if (blocks[destination][index - 1] is not ManagedAssignment previous || !ReadOnly(previous.Value)
                        || previous.Target.Variable == local.Variable || previous.Target.Variable == read.Target.Variable
                        || ManagedValues.Walk(previous.Value).OfType<LocalValue>().Any(v => v.Variable == read.Target.Variable)) break;
                    index--; crossed = true;
                    continue;
                }
                if (handlers.Contains(destination) || incoming.GetValueOrDefault(destination) is not [var predecessor]
                    || !visited.Add(predecessor) || !SameRegion(source.Address, predecessor)) break;
                var terminal = blocks[predecessor].LastOrDefault();
                if (terminal is ManagedBranch branch && snapshot is not null && ReadOnly(branch.Condition)
                    && !CallResult(branch.Condition, []) && branch.Taken.Copies.Count == 0 && branch.Fallthrough.Copies.Count == 0)
                { branched = true; crossed = true; }
                else if (terminal is not ManagedJump { Edge: { Copies.Count: 0 } edge } || edge.Target != destination) break;
                destination = predecessor;
                index = blocks[predecessor].Count - 1;
            }
            if (!crossed) continue;
            if (branched)
            {
                // 未取元素的分支只多读本地结构体字段；原目标仍在原位置写入。
                var temporary = snapshot!(field);
                blocks[source.Address][sourceIndex] = read with { Value = temporary };
                blocks[destination].Insert(index, read with { Target = temporary });
            }
            else
            {
                blocks[source.Address].RemoveAt(sourceIndex);
                blocks[destination].Insert(index, read);
            }
        }
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = blocks[b.Address] }).ToArray() };
    }
}
