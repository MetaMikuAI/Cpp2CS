using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>若干布尔字段守卫通过后写入一个标记，并返回是否写入。</summary>
internal sealed record SourceGuardedUpdate(MethodRef Method, IReadOnlyList<(FieldRef Field, bool Required)> Guards,
    FieldRef Updated, ConstantValue Value)
{
    private static ManagedValue Strip(ManagedValue value)
    {
        while (value is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Width: >= 8 } conversion)
            value = conversion.Operand;
        return value;
    }

    private static (FieldValue Field, bool TakenValue)? Guard(ManagedValue condition, ManagedTypes types)
    {
        if (condition is FieldValue direct && types.Kind(direct.Type) == TypeKind.Bool) return (direct, true);
        if (condition is not ComparisonValue { Condition: Cond.Eq or Cond.Ne, Right: ConstantValue { Bits: 0 } } comparison
            || Strip(comparison.Left) is not FieldValue field || types.Kind(field.Type) != TypeKind.Bool) return null;
        return (field, comparison.Condition == Cond.Ne);
    }

    internal static SourceGuardedUpdate? Create(ManagedBody body, ManagedTypes types)
    {
        if (body.Regions.Count != 0 || body.Blocks.Count is 0 or > 16 || body.Method.Method.IsStatic
            || body.Method.Method.Parameters.Count != 0 || types.Kind(body.Method.Method.ReturnType) != TypeKind.Bool) return null;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var visited = new HashSet<ulong>();
        var path = new HashSet<ulong>();
        var guards = new List<(FieldRef, bool)>();
        var block = body.Blocks[0];
        bool False(ManagedEdge edge)
        {
            var seen = new HashSet<ulong>();
            while (edge.Copies.Count == 0 && seen.Add(edge.Target) && blocks.TryGetValue(edge.Target, out var failure))
            {
                visited.Add(failure.Address);
                if (failure.Statements is [ManagedReturn { Value: ConstantValue { Bits: 0 } }]) return true;
                if (failure.Statements is not [ManagedJump jump]) return false;
                edge = jump.Edge;
            }
            return false;
        }
        while (path.Add(block.Address))
        {
            visited.Add(block.Address);
            if (block.Statements is [ManagedJump { Edge.Copies.Count: 0 } jump] && blocks.TryGetValue(jump.Edge.Target, out block!)) continue;
            if (block.Statements is [ManagedBranch { Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0 } branch]
                && Guard(branch.Condition, types) is { Field.Receiver: ArgumentValue { Index: -1 } } guard)
            {
                var taken = False(branch.Taken);
                var fallthrough = False(branch.Fallthrough);
                if (taken == fallthrough) return null;
                guards.Add((guard.Field.Field, taken != guard.TakenValue));
                if (guards.Count > 8 || !blocks.TryGetValue((taken ? branch.Fallthrough : branch.Taken).Target, out block!)) return null;
                continue;
            }
            if (guards.Count != 0 && block.Statements is [ManagedStore
                    { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } } field, Value: ConstantValue { Bits: 0 or 1 } value },
                    ManagedReturn { Value: ConstantValue { Bits: 1 } }]
                && types.Kind(field.Type) == TypeKind.Bool && value.Type.Equals(field.Type) && visited.Count == blocks.Count)
                return new(body.Method, guards, field.Field, value);
            return null;
        }
        return null;
    }

    internal ManagedBody? Rewrite(ManagedBody body, ManagedTypes types, Func<LocalValue> result, Action<ulong, MethodRef> matched,
        Func<MethodRef, FieldRef?>? getter = null)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var incoming = body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges)
            .GroupBy(e => e.Target).ToDictionary(g => g.Key, g => g.Count());
        var uses = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
        foreach (var region in body.Regions) incoming[region.HandlerEntry] = incoming.GetValueOrDefault(region.HandlerEntry) + 2;
        bool SameRegion(ulong a, ulong b) => body.Regions.All(r => r.Try.Contains(a) == r.Try.Contains(b) && r.Handler.Contains(a) == r.Handler.Contains(b));
        ulong Exit(ManagedEdge edge)
        {
            var seen = new HashSet<ulong>();
            while (edge.Copies.Count == 0 && seen.Add(edge.Target) && blocks.TryGetValue(edge.Target, out var b)
                && b.Statements is [ManagedJump { Edge.Copies.Count: 0 } jump]) edge = jump.Edge;
            return edge.Target;
        }
        foreach (var first in body.Blocks)
        {
            if (first.Statements.LastOrDefault() is not ManagedBranch firstBranch
                || Guard(firstBranch.Condition, types) is not { } initial || !initial.Field.Field.Equals(Guards[0].Field)
                || initial.Field.Receiver is not (LocalValue or ArgumentValue)) continue;
            var receiver = initial.Field.Receiver;
            if (!ManagedAccess.Method(types, body.Method.Method.Owner, Method, receiver.Type)) continue;
            var block = first;
            ManagedEdge? failure = null;
            var removed = new HashSet<ulong>();
            var valid = true;
            foreach (var (field, required) in Guards)
            {
                if (block.Statements.LastOrDefault() is not ManagedBranch
                    { Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0 } branch) { valid = false; break; }
                var condition = branch.Condition;
                if (block != first && block.Statements.Count != 1)
                {
                    // 已认回的访问器可能保留为字段读取快照；仅当局部只供当前条件使用时吸收。
                    var snapshot = block.Statements is [ManagedAssignment assignment, ManagedBranch] && Strip(assignment.Value) is FieldValue
                        ? (assignment.Target, assignment.Value)
                        : block.Statements is [ManagedCall { Tail: false, Inlined: true, Result: { } readResult,
                            Invocation: { Virtual: false, Receiver: { } instance, Arguments.Count: 0 } invocation }, ManagedBranch]
                            && getter?.Invoke(invocation.Method) is { } storage
                            ? (readResult, (ManagedValue)new FieldValue(instance, storage, readResult.Type, readResult.Width)) : default;
                    if (snapshot.Item1 is null || uses.GetValueOrDefault(snapshot.Item1.Variable) != 1) { valid = false; break; }
                    ManagedValue Replace(ManagedValue value) => value is LocalValue local && local.Variable == snapshot.Item1.Variable
                        ? snapshot.Item2 : ManagedValues.Map(value, Replace);
                    condition = Replace(condition);
                }
                if (Guard(condition, types) is not { } guard || !guard.Field.Field.Equals(field)
                    || !guard.Field.Receiver.Equals(receiver)) { valid = false; break; }
                var pass = required == guard.TakenValue ? branch.Taken : branch.Fallthrough;
                var fail = required == guard.TakenValue ? branch.Fallthrough : branch.Taken;
                if (failure is not null && Exit(failure) != Exit(fail)) { valid = false; break; }
                failure ??= fail;
                if (block != first) removed.Add(block.Address);
                var seen = new HashSet<ulong>();
                while (seen.Add(pass.Target) && incoming.GetValueOrDefault(pass.Target) == 1
                    && SameRegion(first.Address, pass.Target) && blocks.TryGetValue(pass.Target, out block!))
                {
                    if (block.Statements is not [ManagedJump { Edge.Copies.Count: 0 } jump]) break;
                    removed.Add(block.Address);
                    pass = jump.Edge;
                }
                if (block.Address != pass.Target || incoming.GetValueOrDefault(block.Address) != 1
                    || !SameRegion(first.Address, block.Address)) { valid = false; break; }
            }
            if (!valid || failure is null || block == first || removed.Contains(block.Address)
                || block.Statements.FirstOrDefault() is not ManagedStore { Target: FieldValue updated, Value: ConstantValue value }
                || !updated.Field.Equals(Updated) || !updated.Receiver.Equals(receiver) || !value.Equals(Value)) continue;
            var returned = result();
            var call = new ManagedCall(firstBranch.Address, new(Method, receiver, [], false), returned, false);
            var replacement = new ManagedBranch(firstBranch.Address, returned, new(block.Address, []), failure);
            var changed = body with
            {
                Blocks = body.Blocks.Where(b => !removed.Contains(b.Address)).Select(b => b == first
                    ? b with { Statements = [.. b.Statements.Take(b.Statements.Count - 1), call, replacement] }
                    : b == block ? b with { Statements = b.Statements.Skip(1).ToArray() } : b).ToArray(),
                Regions = body.Regions.Select(r => r with { Try = r.Try.Where(a => !removed.Contains(a)).ToArray(),
                    Handler = r.Handler.Where(a => !removed.Contains(a)).ToArray() }).ToArray(),
            };
            matched(firstBranch.Address, Method);
            return changed;
        }
        return null;
    }
}
