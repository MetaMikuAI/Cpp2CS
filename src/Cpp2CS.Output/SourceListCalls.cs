using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>List 内联操作的字段读写和分支结构，合并为公开调用。</summary>
internal static partial class SourceListCalls
{
    public static ManagedBody Rewrite(ManagedBody body, ManagedTypes types, Action<ulong, MethodRef> matched)
    {
        while ((MatchAdd(body, types, matched) ?? MatchClear(body, types, matched)) is { } rewritten) body = rewritten;
        return body;
    }

    private sealed class PatternFlow
    {
        private readonly ManagedBody body;
        private readonly Dictionary<ulong, ManagedBlock> blocks;
        public Dictionary<ulong, int> Predecessors { get; }

        public PatternFlow(ManagedBody body)
        {
            this.body = body;
            blocks = body.Blocks.ToDictionary(b => b.Address);
            Predecessors = body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges)
                .GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Count());
            foreach (var region in body.Regions) Predecessors[region.HandlerEntry] = Predecessors.GetValueOrDefault(region.HandlerEntry) + 2;
        }
        public bool SameRegion(ulong a, ulong b) => body.Regions.All(r => r.Try.Contains(a) == r.Try.Contains(b) && r.Handler.Contains(a) == r.Handler.Contains(b));

        // 只穿过单入口直线块，不跨异常边界；共享后继保留为退出边。
        public IEnumerable<ManagedStatement> Straight(ulong entry, int start, ulong region)
        {
            var seen = new HashSet<ulong>();
            while (seen.Add(entry) && blocks.TryGetValue(entry, out var block) && SameRegion(entry, region))
            {
                for (var i = start; i < block.Statements.Count; i++)
                {
                    var s = block.Statements[i];
                    if (s is ManagedJump { Edge: { Copies.Count: 0 } edge } && Predecessors.GetValueOrDefault(edge.Target) == 1 && SameRegion(entry, edge.Target))
                    { entry = edge.Target; start = -1; break; }
                    yield return s;
                }
                if (start != -1) yield break;
                start = 0;
            }
        }
    }

    private static ManagedBody? MatchAdd(ManagedBody body, ManagedTypes types, Action<ulong, MethodRef> matched)
    {
        var list = types.CorlibDefinition("System.Collections.Generic.List");
        if (list is null) return null;
        var flow = new PatternFlow(body);

        foreach (var block in body.Blocks)
        for (var start = 0; start < block.Statements.Count; start++)
        {
            if (block.Statements[start] is not ManagedAssignment first || Strip(first.Value) is not FieldValue field
                || field.Field.Field.Name is not ("_items" or "_version") || field.Field.Field.Owner != list
                || field.Receiver is not (LocalValue or ArgumentValue) || field.Receiver.Type is not DefinitionRef { Arguments.Count: 1 } owner) continue;
            var receiver = field.Receiver;
            var values = new Dictionary<Variable, ManagedValue>();
            var remove = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
            var locals = new HashSet<Variable>();
            ManagedValue Resolve(ManagedValue value)
            {
                value = Strip(value);
                if (value is LocalValue local && values.TryGetValue(local.Variable, out var known)) return known;
                return ManagedValues.Map(value, Resolve);
            }
            bool IsField(ManagedValue value, string name) => value is FieldValue f && f.Receiver.Equals(receiver)
                && f.Field.DeclaringType.Equals(owner) && f.Field.Field.Name == name;
            bool Increment(ManagedValue value, ManagedValue original) => value is BinaryValue { Op: BinOp.Add, Right: ConstantValue { Bits: 1 } } add && add.Left.Equals(original);
            bool Assign(ManagedAssignment assignment)
            {
                if (locals.Contains(assignment.Target.Variable)) return false;
                var value = Resolve(assignment.Value);
                if (ManagedValues.Walk(value).Any(v => v is not (FieldValue or LocalValue or ArgumentValue or ConstantValue or BinaryValue or ConversionValue or ArrayLengthValue)
                    || v is FieldValue f && !(IsField(f, "_items") || IsField(f, "_size") || IsField(f, "_version"))
                    || v is BinaryValue { Op: not BinOp.Add } || v is ArrayLengthValue length && !IsField(length.Array, "_items"))) return false;
                values[assignment.Target.Variable] = value;
                locals.Add(assignment.Target.Variable);
                remove.Add(assignment);
                return true;
            }
            using var prefix = flow.Straight(block.Address, start, block.Address).GetEnumerator();
            ManagedBranch? branch = null;
            var version = false;
            while (prefix.MoveNext())
            {
                var statement = prefix.Current;
                if (statement is ManagedAssignment assignment && Assign(assignment)) continue;
                if (!version && statement is ManagedStore store && IsField(store.Target, "_version") && Increment(Resolve(store.Value), store.Target))
                { version = true; remove.Add(store); continue; }
                branch = statement as ManagedBranch;
                break;
            }
            if (!version || branch is not { Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0 }
                || Resolve(branch.Condition) is not ComparisonValue { Condition: Cond.Ult or Cond.Uge } condition
                || !IsField(condition.Left, "_size") || condition.Right is not ArrayLengthValue length || !IsField(length.Array, "_items")) continue;
            var fastEdge = condition.Condition == Cond.Ult ? branch.Taken : branch.Fallthrough;
            var slowEdge = condition.Condition == Cond.Ult ? branch.Fallthrough : branch.Taken;
            if (flow.Predecessors.GetValueOrDefault(fastEdge.Target) != 1 || flow.Predecessors.GetValueOrDefault(slowEdge.Target) != 1
                || !flow.SameRegion(block.Address, fastEdge.Target) || !flow.SameRegion(block.Address, slowEdge.Target)) continue;
            using var fast = flow.Straight(fastEdge.Target, 0, block.Address).GetEnumerator();
            ManagedStatement? Next(IEnumerator<ManagedStatement> path)
            {
                while (path.MoveNext())
                {
                    if (path.Current is ManagedAssignment a && Assign(a)) continue;
                    return path.Current;
                }
                return null;
            }
            if (Next(fast) is not ManagedStore size || !IsField(size.Target, "_size") || !Increment(Resolve(size.Value), condition.Left)) continue;
            if (Next(fast) is not ManagedStore { Target: ArrayElementValue element } write
                || !Resolve(element.Array).Equals(length.Array) || !Resolve(element.Index).Equals(condition.Left)) continue;
            var item = write.Value;
            // 参数须为进入内联区域前已求值的快照，不把有副作用的取值提前。
            bool Snapshot(ManagedValue value) => value switch
            {
                LocalValue l => !locals.Contains(l.Variable),
                ArgumentValue or ConstantValue or StringValue => true,
                ConversionValue c => Snapshot(c.Operand),
                // 按值保存的结构体字段仍属于快照；不沿引用字段或 ref 参数继续读取对象。
                FieldValue f when (f.Receiver is AddressValue a ? a.Target : f.Receiver) is var root
                    && types.Kind(root.Type) == TypeKind.Struct => Snapshot(root),
                _ => false,
            };
            if (!Snapshot(item)) continue;
            var fastExit = Next(fast);
            using var slow = flow.Straight(slowEdge.Target, 0, block.Address).GetEnumerator();
            if (!slow.MoveNext() || slow.Current is not ManagedCall { Result: null, Invocation: { Arguments.Count: 1 } invocation } resize
                || invocation.Method.Method.Name != "AddWithResize" || !invocation.Method.DeclaringType.Equals(owner)
                || !Equals(invocation.Receiver, receiver) || !invocation.Arguments[0].Equals(item)) continue;
            var slowExit = resize.Tail ? new ManagedReturn(resize.Address, null) : slow.MoveNext() ? slow.Current : null;
            if (!SameExit(fastExit, slowExit)) continue;
            remove.Add(size); remove.Add(write); remove.Add(resize); remove.Add(branch);
            if (body.Blocks.SelectMany(b => b.Statements).Where(s => !remove.Contains(s))
                .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                .OfType<LocalValue>().Any(l => locals.Contains(l.Variable))) continue;
            var add = list.Methods.SingleOrDefault(m => m.Name == "Add" && !m.IsStatic && m.Parameters.Count == 1
                && ManagedTypes.IsVoid(m.ReturnType) && m.Parameters[0].Type.Substitute(owner.Arguments, []).Equals(element.Type));
            if (add is null) continue;
            var method = new MethodRef(add, owner.Arguments, []);
            if (!ManagedAccess.Method(types, body.Method.Method.Owner, method, receiver.Type)) continue;
            var call = new ManagedCall(first.Address, new ManagedInvocation(method, receiver, [item], true), null, false);
            var rewritten = body with
            {
                Blocks = body.Blocks.Select(b => b with
                {
                    Statements = b.Statements.SelectMany(s => ReferenceEquals(s, first) ? new ManagedStatement[] { call }
                        : ReferenceEquals(s, branch) ? [new ManagedJump(branch.Address, fastEdge)] : remove.Contains(s) ? [] : [s]).ToArray(),
                }).ToArray(),
            };
            matched(first.Address, method);
            return Prune(rewritten);
        }
        return null;
    }

    private static ManagedValue Strip(ManagedValue value)
    {
        while (value is ConversionValue { Kind: ConvKind.Truncate or ConvKind.ZeroExtend or ConvKind.SignExtend, Width: >= 32, Operand.Width: >= 32 } conversion)
            value = conversion.Operand;
        return value;
    }

    private static bool SameExit(ManagedStatement? left, ManagedStatement? right) => (left, right) switch
    {
        (ManagedReturn { Value: null }, ManagedReturn { Value: null }) => true,
        (ManagedJump a, ManagedJump b) => a.Edge.Target == b.Edge.Target && a.Edge.Copies.SequenceEqual(b.Edge.Copies),
        _ => false,
    };

    private static ManagedBody Prune(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var reachable = new HashSet<ulong>();
        var pending = new Stack<ulong>([body.Blocks[0].Address]);
        while (true)
        {
            while (pending.TryPop(out var address))
                if (reachable.Add(address))
                    foreach (var edge in blocks[address].Statements.SelectMany(ManagedValues.Edges)) pending.Push(edge.Target);
            var handlers = body.Regions.Where(r => r.Try.Any(reachable.Contains) && !reachable.Contains(r.HandlerEntry)).Select(r => r.HandlerEntry).ToArray();
            if (handlers.Length == 0) break;
            foreach (var handler in handlers) pending.Push(handler);
        }
        return body with
        {
            Blocks = body.Blocks.Where(b => reachable.Contains(b.Address)).ToArray(),
            Regions = body.Regions.Where(r => r.Try.Any(reachable.Contains)).Select(r => r with
            { Try = r.Try.Where(reachable.Contains).ToArray(), Handler = r.Handler.Where(reachable.Contains).ToArray() }).ToArray(),
        };
    }
}
