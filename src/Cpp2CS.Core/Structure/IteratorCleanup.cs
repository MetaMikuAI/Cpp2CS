using Cpp2CS.Ir;
using Cpp2CS.Recovery;
using Cpp2CS.Model;

namespace Cpp2CS.Structure;

/// <summary>把迭代器的捕获、清理、重抛序列还原为 CIL fault，供源码反编译识别。</summary>
internal static class IteratorCleanup
{
    public static ManagedBody Rewrite(ManagedBody body)
    {
        var method = body.Method.Method;
        if (!EnumerationProtocol.IteratorMoveNext(method)) return body;
        var outer = body.Regions.Where(r => r is { Kind: ManagedRegionKind.Catch, CatchType: null, Exception: not null }
            && body.Regions.Where(n => n != r).All(n => n.Try.Concat(n.Handler).All(r.Try.Contains))).ToArray();
        if (outer is not [var region]) return body;
        var exception = region.Exception!;
        var nested = body.Regions.Where(r => r != region).ToArray();

        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var aliases = new Dictionary<Variable, ManagedValue>();
        var handler = new HashSet<ulong>();
        ManagedCall? cleanup = null;
        ManagedValue Expand(ManagedValue value) => value is LocalValue local && aliases.TryGetValue(local.Variable, out var source) ? source : value;
        bool Caught(ManagedValue value) => Expand(value) is LocalValue local && local.Variable == exception.Variable;
        void Copy(ManagedEdge edge)
        {
            var values = edge.Copies.Select(c => (c.Target.Variable, Value: Expand(c.Value))).ToArray();
            foreach (var (variable, value) in values) aliases[variable] = value;
        }
        var current = region.HandlerEntry;
        var rethrows = false;
        while (!rethrows && handler.Add(current))
        {
            if (!blocks.TryGetValue(current, out var block)) return body;
            ManagedEdge? next = null;
            foreach (var statement in block.Statements)
            {
                switch (statement)
                {
                    case ManagedAssignment assignment when Expand(assignment.Value) is LocalValue or ArgumentValue or ConstantValue:
                        aliases[assignment.Target.Variable] = Expand(assignment.Value);
                        break;
                    case ManagedJump jump:
                        next = jump.Edge;
                        break;
                    // 捕获到的托管异常非空；IL2CPP 为原生异常留下的空分支不属于这个 handler。
                    case ManagedBranch { Condition: ComparisonValue { Condition: Cond.Eq or Cond.Ne, Right: ConstantValue { Bits: 0 } } test } branch
                        when Caught(test.Left):
                        next = test.Condition == Cond.Ne ? branch.Taken : branch.Fallthrough;
                        break;
                    case ManagedCall { Result: null, Tail: false, Invocation: { Arguments.Count: 0 } invocation } call
                        when cleanup is null && EnumerationProtocol.IteratorDispose(invocation.Method.Method, method.Owner)
                            && invocation.Receiver is { } receiver && Expand(receiver) is ArgumentValue { Index: -1 }:
                        cleanup = call with { Invocation = invocation with { Receiver = Expand(receiver) } };
                        break;
                    case ManagedThrow thrown when Caught(thrown.Exception):
                    case ManagedRethrow when region.Handler.Contains(current):
                        rethrows = true;
                        break;
                    default:
                        return body;
                }
            }
            if (rethrows) break;
            if (next is null) return body;
            Copy(next);
            current = next.Target;
        }
        if (!rethrows || cleanup is null) return body;

        var normal = new HashSet<ulong>();
        var pending = new Stack<ulong>();
        pending.Push(body.Blocks[0].Address);
        while (pending.TryPop(out var address))
        {
            if (handler.Contains(address)) return body;
            if (!normal.Add(address)) continue;
            foreach (var edge in blocks[address].Statements.SelectMany(ManagedValues.Edges)) pending.Push(edge.Target);
            foreach (var inner in nested.Where(r => r.Try.Contains(address))) pending.Push(inner.HandlerEntry);
        }
        // 原生 EH 只覆盖会抛出的指令。把外围的状态写入、复制和返回纳入同一个 try，不能新增可抛出的操作。
        static bool Harmless(ManagedValue value) => value switch
        {
            ArgumentValue or LocalValue or ConstantValue => true,
            FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null } => true,
            AddressValue { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null } } => true,
            ComposedValue composed => composed.Leaves.All(l => Harmless(l.Value)),
            ConversionValue or ComparisonValue or NegatedValue or BooleanValue => ManagedValues.Children(value).All(Harmless),
            BinaryValue { Op: BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Add or BinOp.Sub } => ManagedValues.Children(value).All(Harmless),
            _ => false,
        };
        bool Safe(ManagedStatement statement) => statement switch
        {
            ManagedAssignment or ManagedReturn or ManagedJump or ManagedBranch =>
                ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).All(Harmless),
            ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null }, Value: var value } => Harmless(value),
            ManagedStore { Target: IndirectValue { Address: AddressValue { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null } } }, Value: var value } => Harmless(value),
            _ => false,
        };
        if (normal.Except(region.Try).Any(a => !blocks[a].Statements.All(Safe))) return body;
        var ordered = body.Blocks.Where(b => normal.Contains(b.Address)).Select(b => blocks[b.Address]).ToArray();
        var fault = new ManagedBlock(region.HandlerEntry, [cleanup, new ManagedEndFault(cleanup.Address)]);
        var resultBody = body with
        {
            Blocks = [.. ordered, fault],
            Regions = [new ManagedRegion(ordered.Select(b => b.Address).ToArray(), fault.Address, [fault.Address], null, ManagedRegionKind.Fault),
                .. nested.Where(r => r.Try.Any(normal.Contains)).Select(r => r with
                { Try = r.Try.Where(normal.Contains).ToArray(), Handler = r.Handler.Where(normal.Contains).ToArray() })],
        };
        return SourceReturns.Rewrite(SplitStateEntries(resultBody));
    }

    // 优化器合并了首次进入与 yield 恢复后的负状态写入；拆开共享入口，保留各自的 finally 边界。
    private static ManagedBody SplitStateEntries(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var incoming = body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges)
            .GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Count());
        var shared = body.Blocks.Where(b => incoming.GetValueOrDefault(b.Address) > 1 && b.Statements is
            [ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Field.Field.Name: "<>1__state" },
                Value: ConstantValue { Bits: > int.MaxValue, Width: 32 } }, ManagedJump { Edge.Copies.Count: 0 }]
            && !body.Regions.Skip(1).Any(r => r.Try.Contains(b.Address) || r.Handler.Contains(b.Address)))
            .ToDictionary(b => b.Address);
        if (shared.Count == 0) return body;
        var output = new List<ManagedBlock>();
        var copies = new List<ManagedBlock>();
        var label = blocks.Keys.Max() + 1;
        foreach (var block in body.Blocks.Where(b => !shared.ContainsKey(b.Address)))
            output.Add(block with { Statements = block.Statements.Select(s => ManagedValues.MapEdges(s, edge =>
            {
                if (!shared.TryGetValue(edge.Target, out var target)) return edge;
                var clone = target with { Address = label++ };
                copies.Add(clone);
                return edge with { Target = clone.Address };
            })).ToArray() });
        var region = body.Regions[0];
        var normal = output.Where(b => region.Try.Contains(b.Address)).Concat(copies).ToArray();
        return body with
        {
            Blocks = [.. normal, .. output.Where(b => region.Handler.Contains(b.Address))],
            Regions = body.Regions.Select(r => r == region ? r with { Try = normal.Select(b => b.Address).ToArray() } : r).ToArray(),
        };
    }
}
