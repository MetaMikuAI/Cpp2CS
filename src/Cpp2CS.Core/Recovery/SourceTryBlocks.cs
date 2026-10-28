using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>把保护区出口处已证明不抛异常的运算归回 try，保留未知访问和其他异常区域。</summary>
internal static class SourceTryBlocks
{
    private static bool Receiver(ManagedValue value, HashSet<ManagedValue> nonnull, Func<MethodRef, bool>? getter) => value switch
    {
        LocalValue or ArgumentValue => nonnull.Contains(value) || value.Type is DefinitionRef { Definition.IsValueType: true },
        AddressValue address => address.Target.Type is DefinitionRef { Definition.IsValueType: true }
            && address.Target is LocalValue or ArgumentValue or FieldValue && Pure(address.Target, nonnull, getter),
        _ => false,
    };

    private static bool Pure(ManagedValue value, HashSet<ManagedValue> nonnull, Func<MethodRef, bool>? getter) => value switch
    {
        LocalValue or ArgumentValue or ConstantValue => true,
        FieldValue field => Receiver(field.Receiver, nonnull, getter)
            && !field.Field.Field.IsStatic && (field.Accessor is null || !field.Accessor.Write && getter?.Invoke(field.Accessor.Method) == true),
        ConversionValue conversion => ManagedTypes.PrimitiveName(conversion.Type) is not null
            && ManagedTypes.PrimitiveName(conversion.Operand.Type) is not null && Pure(conversion.Operand, nonnull, getter),
        BinaryValue { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor
            or BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv } binary
            => Pure(binary.Left, nonnull, getter) && Pure(binary.Right, nonnull, getter),
        ComparisonValue comparison => Pure(comparison.Left, nonnull, getter) && Pure(comparison.Right, nonnull, getter),
        ChoiceValue choice => Pure(choice.Condition, nonnull, getter) && Pure(choice.True, nonnull, getter) && Pure(choice.False, nonnull, getter),
        BooleanValue boolean => Pure(boolean.Left, nonnull, getter) && Pure(boolean.Right, nonnull, getter),
        NegatedValue negated => Pure(negated.Operand, nonnull, getter),
        _ => false,
    };

    internal static ManagedBody Rewrite(ManagedBody body, Func<MethodRef, bool>? getter = null)
    {
        if (body.Regions.Count == 0 || body.Blocks.Any(b => b.Statements.LastOrDefault() is not
            (ManagedJump or ManagedBranch or ManagedSwitch or ManagedReturn or ManagedThrow or ManagedRethrow or ManagedEndFault))) return body;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var order = body.Blocks.Select(b => b.Address).ToList();
        var regions = body.Regions.ToArray();
        var nonnull = SourceNonNullReceivers.Read(body, getter);
        bool NonThrowing(ManagedBlock block) => block.Statements.All(s => (s switch
        {
            ManagedAssignment assignment => Pure(assignment.Value, nonnull[s], getter),
            ManagedStore { Target: FieldValue { Accessor: null } field } store
                => ManagedTypes.PrimitiveName(field.Type) is "Boolean" or "Char" or "SByte" or "Byte" or "Int16" or "UInt16"
                        or "Int32" or "UInt32" or "Int64" or "UInt64" or "Single" or "Double"
                    && Pure(field, nonnull[s], getter) && Pure(store.Value, nonnull[s], getter),
            ManagedJump or ManagedBranch or ManagedSwitch or ManagedReturn => ManagedValues.Of(s).All(v => Pure(v, nonnull[s], getter)),
            ManagedCall { Invocation: { Receiver: { } receiver, Arguments.Count: 0 } invocation } when getter is not null
                => getter(invocation.Method) && Receiver(receiver, nonnull[s], getter),
            _ => false,
        }) && ManagedValues.Edges(s).SelectMany(e => e.Copies).All(c => Pure(c.Value, nonnull[s], getter)));
        foreach (var index in Enumerable.Range(0, regions.Length).OrderBy(i => regions[i].Try.Count))
        {
            var region = regions[index];
            var members = region.Try.ToHashSet();
            var pending = new Queue<ulong>(region.Try);
            while (pending.TryDequeue(out var source))
                foreach (var target in blocks[source].Statements.SelectMany(ManagedValues.Edges).Select(e => e.Target).Distinct())
                {
                    if (members.Contains(target) || region.Handler.Contains(target) || target == body.Blocks[0].Address
                        || !blocks.TryGetValue(target, out var block) || !NonThrowing(block)
                        || regions.Where((_, i) => i != index).Any(r => r.Try.Contains(target) && !r.Try.All(members.Contains)
                            && !region.Try.All(r.Try.Contains) || r.Handler.Contains(target) && !r.Handler.All(members.Contains)
                            && !region.Try.All(r.Handler.Contains))) continue;
                    members.Add(target); pending.Enqueue(target);
                }
            if (members.Count == region.Try.Count) continue;
            var entries = body.Blocks.Where(b => !members.Contains(b.Address))
                .SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges)).Select(e => e.Target)
                .Where(members.Contains).Distinct().ToArray();
            if (entries.Length != 1) continue;
            var added = order.Where(a => members.Contains(a) && !region.Try.Contains(a)).ToArray();
            var arranged = order.Except(added).ToList();
            if (added.Contains(entries[0])) arranged.Insert(arranged.FindIndex(region.Try.Contains), entries[0]);
            arranged.InsertRange(arranged.FindLastIndex(region.Try.Contains) + 1, added.Where(a => a != entries[0]));
            var positions = arranged.Select((a, i) => (a, i)).ToDictionary(p => p.a, p => p.i);
            bool Contiguous(IEnumerable<ulong> addresses)
            {
                var indices = addresses.Select(a => positions[a]).ToArray();
                return indices.Length > 0 && indices.Max() - indices.Min() + 1 == indices.Length;
            }
            var updated = region with { Try = arranged.Where(members.Contains).ToArray() };
            var candidate = regions.Select((r, i) => i == index ? updated : r).ToArray();
            var ranges = candidate.SelectMany(r => new[] { r.Try, r.Handler }).ToArray();
            if (ranges.Any(r => !Contiguous(r)) || ranges.Any(a => ranges.Any(b => a.Intersect(b).Any()
                && !a.All(b.Contains) && !b.All(a.Contains)))) continue;
            // 新纳入的块不能成为保护区中途的外部入口。
            if (entries[0] != updated.Try[0]) continue;
            order = arranged; regions[index] = updated;
        }
        return body with
        {
            Blocks = order.Select(a => blocks[a]).ToArray(),
            Regions = regions.Select(r => r with { Try = order.Where(r.Try.Contains).ToArray(), Handler = order.Where(r.Handler.Contains).ToArray() }).ToArray(),
        };
    }
}
