using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>将 null 旁路及同一引用的类型检查还原为 castclass，保持异常区域与求值次数。</summary>
internal static class SourceCheckedCasts
{
    internal static ManagedBody Rewrite(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var predecessors = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges)
            .Select(e => (e.Target, From: b.Address))).ToLookup(e => e.Target, e => e.From);
        var changed = false;
        foreach (var original in body.Blocks)
        {
            var guard = blocks[original.Address];
            if (guard.Statements.LastOrDefault() is not ManagedBranch
                {
                    Condition: ComparisonValue condition,
                    Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0
                } branch
                || condition is not { Left: LocalValue or ArgumentValue, Right: ConstantValue { Bits: 0 }, Condition: Cond.Eq or Cond.Ne }
                || !ManagedTypes.IsReferenceType(condition.Left.Type)) continue;
            var value = condition.Left;
            var join = condition.Condition == Cond.Eq ? branch.Taken.Target : branch.Fallthrough.Target;
            var current = condition.Condition == Cond.Eq ? branch.Fallthrough.Target : branch.Taken.Target;
            if (!blocks.TryGetValue(join, out var merged) || merged.Statements.FirstOrDefault() is not ManagedAssignment
                { Value: IsInstValue { BoxedType: null, Target: DefinitionRef { Definition.IsValueType: false } or ArrayRef } cast } result
                || cast.Operand != value || !SameRegion(guard.Address, join)) continue;
            var path = new List<ManagedBlock>();
            var previous = guard.Address;
            while (current != join && path.Count < 64 && blocks.TryGetValue(current, out var block)
                && !path.Any(b => b.Address == current) && predecessors[current].ToArray() is [var from] && from == previous
                && SameRegion(current, join) && block.Statements.LastOrDefault() is ManagedJump { Edge.Copies.Count: 0 } jump)
            {
                path.Add(block); previous = current; current = jump.Edge.Target;
            }
            if (current != join || path.Count == 0 || predecessors[join].Distinct().Order().SequenceEqual(new[] { guard.Address, previous }.Order()) == false) continue;
            var aliases = new Dictionary<Variable, ManagedValue>();
            var checks = 0;
            var valid = true;
            ManagedValue Expand(ManagedValue item, int depth = 0) => depth > 24 ? item : item is LocalValue local && aliases.TryGetValue(local.Variable, out var source)
                ? Expand(source, depth + 1) : ManagedValues.Map(item, v => Expand(v, depth + 1));
            foreach (var statement in path.SelectMany(b => b.Statements.Take(b.Statements.Count - 1)))
            {
                if (statement is ManagedAssignment assignment && assignment.Target != value && !aliases.ContainsKey(assignment.Target.Variable)
                    && Safe(Expand(assignment.Value), value, cast.Target)) aliases.Add(assignment.Target.Variable, Expand(assignment.Value));
                else if (statement is ManagedCheck { Exception.Method.Owner.FullName: "System.InvalidCastException" } check
                    && Matches(Expand(check.Condition), value, cast.Target) == false) checks++;
                else { valid = false; break; }
            }
            if (!valid || checks == 0) continue;
            var removed = path.Select(b => b.Address).ToHashSet();
            // 处理路径中的临时值不能被外部或异常处理读取，也不能通过地址逸出。
            if (body.Regions.Any(r => r.Exception is { } exception && aliases.ContainsKey(exception.Variable))
                || blocks.Values.Where(b => !removed.Contains(b.Address)).SelectMany(b => b.Statements)
                    .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                    .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => aliases.ContainsKey(l.Variable))) continue;
            blocks[guard.Address] = guard with { Statements = [.. guard.Statements.Take(guard.Statements.Count - 1), new ManagedJump(branch.Address, new(join, []))] };
            foreach (var block in path) blocks[block.Address] = block with { Statements = [new ManagedJump(block.Statements[^1].Address, new(join, []))] };
            blocks[join] = merged with { Statements = [result with { Value = new CheckedCastValue(value, cast.Target) }, .. merged.Statements.Skip(1)] };
            changed = true;
        }
        return changed ? body with { Blocks = body.Blocks.Select(b => blocks[b.Address]).ToArray() } : body;

        bool SameRegion(ulong left, ulong right) => body.Regions.All(r => r.Try.Contains(left) == r.Try.Contains(right)
            && r.Handler.Contains(left) == r.Handler.Contains(right) && r.HandlerEntry != left && r.HandlerEntry != right);
    }

    private static bool Safe(ManagedValue value, ManagedValue source, TypeRef target) => value == source || value switch
    {
        ConstantValue => true,
        IsInstValue test => test.BoxedType is null && test.Operand == source && test.Target.Equals(target),
        ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: var operand } => Safe(operand, source, target),
        ComparisonValue { Condition: Cond.Eq or Cond.Ne } comparison => Safe(comparison.Left, source, target) && Safe(comparison.Right, source, target),
        BinaryValue { Op: BinOp.And, Right: ConstantValue { Bits: 1 }, Left: var left } => Safe(left, source, target),
        NegatedValue negated => Safe(negated.Operand, source, target),
        _ => false,
    };

    // 返回该条件为真时是否表示类型匹配；不把任意整数视为布尔值。
    private static bool? Matches(ManagedValue value, ManagedValue source, TypeRef target) => value switch
    {
        ComparisonValue { Condition: Cond.Eq or Cond.Ne, Left: IsInstValue test, Right: ConstantValue { Bits: 0 } } comparison
            when test.BoxedType is null && test.Operand == source && test.Target.Equals(target) => comparison.Condition == Cond.Ne,
        ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: var operand } => Matches(operand, source, target),
        BinaryValue { Op: BinOp.And, Right: ConstantValue { Bits: 1 }, Left: var left } => Matches(left, source, target),
        ComparisonValue { Condition: Cond.Eq or Cond.Ne, Right: ConstantValue { Bits: 0 } } comparison
            when Matches(comparison.Left, source, target) is { } matched => comparison.Condition == Cond.Ne ? matched : !matched,
        NegatedValue negated when Matches(negated.Operand, source, target) is { } matched => !matched,
        _ => null,
    };
}
