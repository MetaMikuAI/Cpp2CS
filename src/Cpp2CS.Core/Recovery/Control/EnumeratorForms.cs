using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// foreach 降级之后被 IL2CPP 和 clang 改变的两处，还原成 IL 的写法：
/// 结构体枚举器的 Dispose 在 IL 里是 constrained callvirt IDisposable.Dispose，IL2CPP 去虚化成直接调用；
/// Current 在 IL 里循环体开头读一次，内联之后 clang 把字段读取沉到各使用处。读取之间枚举器没有被改写时，它们是同一个值。
/// </summary>
internal static class EnumeratorForms
{
    public static ManagedBody Run(ManagedBody body)
    {
        // 新局部不能和任何已有的局部同名，包括只写不读的调用结果和边上复制的目标。
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var locals = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk).OfType<LocalValue>()
            .Concat(statements.OfType<ManagedCall>().Select(c => c.Result).OfType<LocalValue>())
            .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target))
            .Concat(body.Regions.Select(r => r.Exception).OfType<LocalValue>());
        var nextLocal = locals.Where(l => l.Variable.Storage.Bank == Bank.Temp).Select(l => l.Variable.Storage.Index).DefaultIfEmpty(1000).Max() + 1;
        foreach (var region in body.Regions.Where(r => r.Kind == ManagedRegionKind.Finally).ToArray())
        {
            body = Constrained(body, region);
            if (HoistCurrent(body, region, nextLocal) is { } hoisted)
            {
                body = hoisted;
                nextLocal++;
            }
        }
        return body;
    }

    private static ManagedBody Constrained(ManagedBody body, ManagedRegion region)
    {
        var handler = region.Handler.ToHashSet();
        ManagedStatement Rewrite(ManagedStatement statement)
        {
            if (statement is not ManagedCall
                {
                    Result: null,
                    Invocation:
                    {
                        Virtual: false, Constraint: null, Arguments.Count: 0, Receiver: AddressValue { Target: LocalValue },
                        Method: { Method: { Name: "Dispose", IsVirtual: true, Owner.IsValueType: true } } method,
                    } invocation,
                } call) return statement;
            if (method.Method.Owner.Interfaces.OfType<DefinitionRef>().FirstOrDefault(i => i.Definition.FullName == "System.IDisposable") is not { } disposable
                || disposable.Definition.Methods.FirstOrDefault(m => m.Name == "Dispose") is not { } dispose) return statement;
            return call with { Invocation = invocation with { Method = new MethodRef(dispose, [], []), Virtual = true, Constraint = method.DeclaringType } };
        }
        return body with
        {
            Blocks = body.Blocks.Select(b => handler.Contains(b.Address) ? b with { Statements = b.Statements.Select(Rewrite).ToArray() } : b).ToArray(),
        };
    }

    private static bool IsCurrent(ManagedValue value, Variable enumerator) =>
        value is FieldValue { Accessor.Method.Method.Name: "get_Current", Receiver: LocalValue local } && local.Variable.Equals(enumerator);

    private static ManagedBody? HoistCurrent(ManagedBody body, ManagedRegion region, int nextLocal)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        if (region.Handler.SelectMany(a => blocks[a].Statements).OfType<ManagedCall>()
            .Select(c => c.Invocation.Receiver).OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().ToArray() is not [var enumerator]) return null;
        var variable = enumerator.Variable;
        var inTry = region.Try.ToHashSet();
        var moves = region.Try.SelectMany(a => blocks[a].Statements).OfType<ManagedCall>()
            .Where(c => c.Invocation.Receiver is AddressValue { Target: LocalValue local } && local.Variable.Equals(variable)).ToArray();
        if (moves is not [{ Invocation.Method.Method.Name: "MoveNext", Result: { } moved } move]) return null;
        // 枚举器的其他用途只能是读 Current。
        var reads = new List<FieldValue>();
        foreach (var statement in region.Try.SelectMany(a => blocks[a].Statements).Where(s => !ReferenceEquals(s, move)))
            foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)))
                if (!Scan(value, variable, reads)) return null;
        if (reads.Count == 0) return null;
        // MoveNext 之后的分支。
        var at = region.Try.First(a => blocks[a].Statements.Contains(move));
        var moveBlock = at;
        var position = blocks[at].Statements.ToList().IndexOf(move) + 1;
        ManagedBranch? branch = null;
        for (var steps = 0; steps < 16 && branch is null; steps++)
        {
            switch (blocks[at].Statements[position])
            {
                case ManagedJump { Edge: { Copies.Count: 0 } edge }: (at, position) = (edge.Target, 0); break;
                case ManagedBranch found: branch = found; break;
                default: return null;
            }
        }
        if (branch is null) return null;
        var edgeIn = branch.Condition switch
        {
            LocalValue local when local.Variable.Equals(moved.Variable) => branch.Taken,
            NegatedValue { Operand: LocalValue local } when local.Variable.Equals(moved.Variable) => branch.Fallthrough,
            _ => null,
        };
        if (edgeIn is null || edgeIn.Copies.Count != 0 || !inTry.Contains(edgeIn.Target)) return null;
        var entry = edgeIn.Target;
        if (body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges).Count(e => e.Target == entry) != 1) return null;
        // 读取都在进入循环体之后、下一次 MoveNext 之前。
        var visited = new HashSet<ulong>();
        var work = new Stack<ulong>();
        work.Push(entry);
        while (work.TryPop(out var address))
            if (address != moveBlock && visited.Add(address) && blocks.TryGetValue(address, out var block))
                foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges)) work.Push(edge.Target);
        var readBlocks = region.Try.Where(a => blocks[a].Statements.Any(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)).SelectMany(ManagedValues.Walk).Any(v => IsCurrent(v, variable))));
        if (readBlocks.Any(a => !visited.Contains(a))) return null;

        var type = reads[0].Type;
        var current = new LocalValue(new Variable(Storage.Temp(nextLocal), 1), type, reads[0].Width);
        ManagedValue Replace(ManagedValue value) => IsCurrent(value, variable) ? current : ManagedValues.Map(value, Replace);
        return body with
        {
            Blocks = body.Blocks.Select(b =>
            {
                if (!inTry.Contains(b.Address)) return b;
                var statements = b.Statements.Select(s => ReferenceEquals(s, move) ? s : ManagedValues.Map(s, Replace)).ToList();
                if (b.Address == entry) statements.Insert(0, new ManagedAssignment(move.Address, current, reads[0]));
                return b with { Statements = statements };
            }).ToArray(),
        };
    }

    /// <summary>值里用到枚举器的地方都是读 Current；顺便收集这些读取。</summary>
    private static bool Scan(ManagedValue value, Variable enumerator, List<FieldValue> reads)
    {
        if (IsCurrent(value, enumerator)) { reads.Add((FieldValue)value); return true; }
        if (value is LocalValue local && local.Variable.Equals(enumerator)) return false;
        return ManagedValues.Children(value).All(child => Scan(child, enumerator, reads));
    }
}
