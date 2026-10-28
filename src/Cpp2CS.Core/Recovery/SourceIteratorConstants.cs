using Cpp2CS.Ir;
using Cpp2CS.Structure;

namespace Cpp2CS.Recovery;

/// <summary>状态等值分支中的宽寄存器副本仍是已知常量，不能成为 yield 之后的业务局部变量。</summary>
internal static class SourceIteratorConstants
{
    public static ManagedBody Rewrite(ManagedBody body)
    {
        if (!EnumerationProtocol.IteratorMoveNext(body.Method.Method)) return body;
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var written = statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable)
            .Concat(statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                .OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable)).ToHashSet();
        var tracked = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).Where(g => g.Count() == 1 && !written.Contains(g.Key))
            .Select(g => g.Single()).Where(a => a.Target.Width == 64 && a.Value is ConversionValue { Kind: ConvKind.ZeroExtend, Width: 64,
                Operand: FieldValue { Width: 32, Accessor: null, Receiver: ArgumentValue { Index: -1 }, Field.Field.Name: "<>1__state" } field }
                && field.Field.Field.Owner == body.Method.Method.Owner).ToDictionary(a => a.Target.Variable, a => a.Target);
        if (tracked.Count == 0) return body;
        var incoming = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (Block: b.Address, Edge: e)))
            .GroupBy(p => p.Edge.Target).ToDictionary(g => g.Key, g => g.ToArray());
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
        var inputs = body.Blocks.ToDictionary(b => b.Address, _ => new Dictionary<Variable, ulong>());
        var outputs = body.Blocks.ToDictionary(b => b.Address, _ => new Dictionary<Variable, ulong>());
        Dictionary<Variable, ulong> Edge(ulong predecessor, ManagedEdge edge)
        {
            var known = new Dictionary<Variable, ulong>(outputs[predecessor]);
            if (blocks[predecessor].Statements.LastOrDefault() is ManagedBranch { Condition: ComparisonValue { Condition: Cond.Eq or Cond.Ne } condition } branch
                && !ReferenceEquals(branch.Taken, branch.Fallthrough)
                && ReferenceEquals(branch.Taken, edge) == (condition.Condition == Cond.Eq))
            {
                var value = condition.Left is ConstantValue ? condition.Right : condition.Left;
                var constant = condition.Left as ConstantValue ?? condition.Right as ConstantValue;
                if (value is ConversionValue { Kind: ConvKind.Truncate, Width: 32, Operand: LocalValue local }
                    && tracked.ContainsKey(local.Variable) && constant is { Width: 32, Bits: <= uint.MaxValue }) known[local.Variable] = constant.Bits;
            }
            return known;
        }
        static void Transfer(Dictionary<Variable, ulong> known, ManagedStatement statement)
        {
            if (statement is ManagedAssignment assignment) known.Remove(assignment.Target.Variable);
        }
        bool changed;
        do
        {
            changed = false;
            foreach (var block in body.Blocks)
            {
                var known = new Dictionary<Variable, ulong>();
                if (!entries.Contains(block.Address) && incoming.TryGetValue(block.Address, out var predecessors))
                {
                    known = Edge(predecessors[0].Block, predecessors[0].Edge);
                    foreach (var predecessor in predecessors.Skip(1))
                    {
                        var other = Edge(predecessor.Block, predecessor.Edge);
                        foreach (var variable in known.Keys.ToArray())
                            if (!other.TryGetValue(variable, out var value) || value != known[variable]) known.Remove(variable);
                    }
                }
                inputs[block.Address] = new(known);
                foreach (var statement in block.Statements) Transfer(known, statement);
                if (known.Count == outputs[block.Address].Count && known.All(p => outputs[block.Address].TryGetValue(p.Key, out var value) && value == p.Value)) continue;
                outputs[block.Address] = known;
                changed = true;
            }
        } while (changed);
        ManagedValue Replace(ManagedValue value, Dictionary<Variable, ulong> known) => value is LocalValue local && known.TryGetValue(local.Variable, out var bits)
            ? new ConstantValue(bits, local.Type, local.Width) : ManagedValues.Map(value, v => Replace(v, known));
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var known = new Dictionary<Variable, ulong>(inputs[block.Address]);
            return block with { Statements = block.Statements.Select(statement =>
            {
                var copied = ManagedValues.MapEdges(statement, edge => edge with { Copies = edge.Copies.Select(c =>
                    c with { Value = Replace(c.Value, Edge(block.Address, edge)) }).ToArray() });
                var result = ManagedValues.Map(copied, value => Replace(value, known), target => target);
                Transfer(known, statement);
                return result;
            }).ToArray() };
        }).ToArray() };
    }
}
