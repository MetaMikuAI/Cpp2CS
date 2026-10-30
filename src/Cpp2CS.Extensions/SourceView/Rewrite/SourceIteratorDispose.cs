using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

using Cpp2CS.Machine.Algebra;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>用同一状态分区证明把 Dispose 的有界位掩码写回等值分派，供迭代器识别。</summary>
internal static class SourceIteratorDispose
{
    internal static ManagedBody Rewrite(ManagedBody body)
    {
        if (body.Regions.Count != 0 || body.Blocks.Count is 0 or > 24) return body;
        var original = body;
        body = ExpandSwitches(body);
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var values = statements.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).ToArray();
        if (ReferenceEquals(original, body) && !values.OfType<BinaryValue>().Any(v => v.Op == BinOp.Shl)
            || statements.SelectMany(ManagedValues.Edges).Any(e => e.Copies.Count != 0)
            || statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).Any(g => g.Count() != 1)) return body;
        var fields = values.OfType<FieldValue>().Distinct().ToArray();
        if (fields is not [FieldValue { Receiver: ArgumentValue { Index: -1 }, Width: 32, Accessor: null, Field.Field.Name: "<>1__state" } state]
            || state.Field.Field.Owner != body.Method.Method.Owner) return body;
        var calls = statements.OfType<ManagedCall>().Distinct().ToArray();
        if (calls.Length == 0 || calls.Any(c => c.Result is not null || c.Invocation is not { Receiver: ArgumentValue { Index: -1 }, Arguments.Count: 0, Virtual: false }
            || c.Invocation.Method.Method.Owner != body.Method.Method.Owner || !ManagedTypes.IsVoid(c.Invocation.Method.Method.ReturnType))) return body;
        var ids = calls.Select((c, i) => (c, Id: (ulong)i + 1)).ToDictionary(p => p.c, p => p.Id);
        var receiver = new Use(new(Storage.Gpr(0), 0), 64);
        Expr Value(ManagedValue value) => value switch
        {
            FieldValue f when f == state => new Load(new Binary(BinOp.Add, receiver, Expr.C(16, 64), 64), 32),
            LocalValue l => new Use(l.Variable, l.Width),
            ConstantValue c => Expr.C(c.Bits, c.Width),
            BinaryValue b when b.Width == 32 && b.Op is BinOp.Add or BinOp.Sub or BinOp.And or BinOp.Shl
                => new Binary(b.Op, Value(b.Left), Value(b.Right), b.Width),
            ConversionValue c when c.Kind is ConvKind.ZeroExtend or ConvKind.Truncate => new Ir.Convert(c.Kind, Value(c.Operand), c.Width),
            ComparisonValue c => new Compare(c.Condition, Value(c.Left), Value(c.Right)),
            BooleanValue b => new Logical(b.IsAnd, Value(b.Left), Value(b.Right)),
            NegatedValue n => new Not(Value(n.Operand)),
            _ => new Unknown("非状态分派值", value.Width),
        };
        Stmt? Statement(ManagedStatement statement) => statement switch
        {
            ManagedAssignment a => new Define(a.Address, a.Target.Variable, Value(a.Value)),
            ManagedBranch b => new Branch(b.Address, Value(b.Condition), b.Taken.Target, b.Fallthrough.Target),
            ManagedJump j => new Jump(j.Address, j.Edge.Target),
            ManagedReturn { Value: null } r => new Return(r.Address),
            ManagedCall c => new Call(c.Address, c.Tail ? CallKind.Tail : CallKind.Direct, Expr.C(ids[c], 64)) { Arguments = [receiver] },
            _ => null,
        };
        // 仅作为状态证明的符号图：固定偏移表示唯一字段，调用编号保留原 ManagedCall 的身份。
        var blocks = new List<Block>();
        foreach (var block in body.Blocks)
        {
            var mapped = block.Statements.Select(Statement).ToArray();
            if (mapped.Any(s => s is null)) return body;
            blocks.Add(new(block.Address) { Statements = mapped.Select(s => s!).ToList() });
        }
        var entry = body.Blocks[0].Address;
        var function = new MachineFunction { Entry = entry, Range = new(entry, entry + 1, CodeRegion.Managed, default), Blocks = blocks };
        if (StateDispatch.Read(function, c => c) is not { } dispatch || dispatch.Otherwise.Length > 1
            || dispatch.Cases.Values.Any(c => c.Length > 1)) return body;
        var cases = dispatch.Cases.Where(p => !p.Value.SequenceEqual(dispatch.Otherwise)).OrderBy(p => unchecked((int)p.Key)).ToArray();
        if (cases.Length == 0) return body;
        var next = body.Blocks.Max(b => b.Address) + 1;
        var decisions = cases.Select((_, i) => i == 0 ? entry : next++).ToArray();
        var end = next++;
        var callBlocks = calls.Select(_ => next++).ToArray();
        ulong Target(ulong[] trace) => trace.Length == 0 ? end : callBlocks[(int)trace[0] - 1];
        var temp = values.OfType<LocalValue>().Where(l => l.Variable.Storage.Bank == Bank.Temp)
            .Select(l => l.Variable.Storage.Index).DefaultIfEmpty(0).Max() + 1;
        var saved = new LocalValue(new(Storage.Temp(temp), 1), state.Type, 32);
        var boolean = statements.OfType<ManagedBranch>().First().Condition.Type;
        var rewritten = new List<ManagedBlock>();
        for (var i = 0; i < cases.Length; i++)
        {
            var test = new ComparisonValue(Cond.Eq, saved, new ConstantValue(cases[i].Key, state.Type, 32), boolean);
            var branch = new ManagedBranch(decisions[i], test, new(Target(cases[i].Value), []),
                new(i + 1 < cases.Length ? decisions[i + 1] : Target(dispatch.Otherwise), []));
            rewritten.Add(new(decisions[i], i == 0 ? [new ManagedAssignment(entry, saved, state), branch] : [branch]));
        }
        for (var i = 0; i < calls.Length; i++) rewritten.Add(new(callBlocks[i], [calls[i] with { Tail = false }, new ManagedReturn(callBlocks[i], null)]));
        rewritten.Add(new(end, [new ManagedReturn(end, null)]));
        return body with { Blocks = rewritten };
    }

    private static ManagedBody ExpandSwitches(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var next = blocks.Keys.Max() + 1;
        var changed = false;
        foreach (var block in body.Blocks)
        {
            if (block.Statements is not [ManagedSwitch selection] || selection.Cases.Count is 0 or > 16
                || selection.Cases.Any(e => e.Copies.Count != 0)
                || ManagedValues.Walk(selection.Index).Any(v => v is not (LocalValue or ConstantValue or BinaryValue or ConversionValue))) continue;
            var predecessors = body.Blocks.Where(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == block.Address)).ToArray();
            if (predecessors is not [var predecessor] || predecessor.Statements.LastOrDefault() is not ManagedBranch
                { Condition: ComparisonValue { Condition: Cond.Ugt, Right: ConstantValue limit } condition } guard
                || !Equals(condition.Left, selection.Index) || limit.Bits != (ulong)selection.Cases.Count - 1
                || guard.Fallthrough.Target != block.Address || guard.Taken.Target == block.Address
                || guard.Taken.Copies.Count != 0 || guard.Fallthrough.Copies.Count != 0) continue;
            // 现有范围守卫保证 switch 下标有效；最后一条等值检查仍回到同一范围外出口。
            var addresses = selection.Cases.Select((_, i) => i == 0 ? block.Address : next++).ToArray();
            for (var i = 0; i < addresses.Length; i++)
            {
                var test = new ComparisonValue(Cond.Eq, selection.Index, new ConstantValue((ulong)i, selection.Index.Type, selection.Index.Width), condition.Type);
                blocks[addresses[i]] = new(addresses[i], [new ManagedBranch(selection.Address, test, selection.Cases[i],
                    i + 1 < addresses.Length ? new(addresses[i + 1], []) : guard.Taken)]);
            }
            changed = true;
        }
        return changed ? body with { Blocks = blocks.Values.ToArray() } : body;
    }
}
