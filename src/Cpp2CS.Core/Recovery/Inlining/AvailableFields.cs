using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 局部变量此刻等于哪个字段的内容或数组、字符串的长度（前向必达数据流）：v = r.f 之后，到 v、r 被改写或这个字段可能被写之前，v 就是 r.f 的当前值。
/// 编译器复用较早的读取、在不改内存的路径上省掉重读时，内联副本里看不到这次读取，比较要靠这个事实。
/// 调用、未知写入和可能运行类构造的访问都清空事实；处理块入口没有事实。
/// </summary>
internal sealed class AvailableFields
{
    private readonly Dictionary<ulong, ManagedBlock> blocks;
    private readonly Dictionary<ulong, Dictionary<Variable, ManagedValue>> entries = [];

    public AvailableFields(ManagedBody body)
    {
        blocks = body.Blocks.ToDictionary(b => b.Address);
        // 内联证明可能已经删掉了处理块，区域信息里的入口不一定还在。
        var handlers = body.Regions.Select(r => r.HandlerEntry).Where(blocks.ContainsKey).ToHashSet();
        var pending = new Queue<ulong>();
        foreach (var start in handlers.Prepend(body.Blocks[0].Address).Distinct())
        {
            entries[start] = [];
            pending.Enqueue(start);
        }
        while (pending.TryDequeue(out var address))
        {
            var facts = new Dictionary<Variable, ManagedValue>(entries[address]);
            foreach (var statement in blocks[address].Statements)
            {
                Apply(statement, facts);
                foreach (var edge in ManagedValues.Edges(statement).Where(e => !handlers.Contains(e.Target)))
                {
                    var arriving = Across(edge, facts);
                    if (!entries.TryGetValue(edge.Target, out var known))
                    {
                        entries[edge.Target] = arriving;
                        pending.Enqueue(edge.Target);
                    }
                    else if (Narrowed(known, arriving)) pending.Enqueue(edge.Target);
                }
            }
        }
    }

    /// <summary>第 index 条语句之前的事实；值是字段读取，或它的转换。</summary>
    public IReadOnlyDictionary<Variable, ManagedValue> At(ulong block, int index)
    {
        if (!entries.TryGetValue(block, out var entry)) return new Dictionary<Variable, ManagedValue>();
        var facts = new Dictionary<Variable, ManagedValue>(entry);
        foreach (var statement in blocks[block].Statements.Take(index)) Apply(statement, facts);
        return facts;
    }

    private static void Apply(ManagedStatement statement, Dictionary<Variable, ManagedValue> facts)
    {
        // 证明过的访问器只读一个字段，调用它不改内存。
        static EffectSummary? Proven(ManagedValue value) => value is FieldValue { Accessor: not null } access ? ManagedEffects.Value(access.Receiver) : null;
        if (ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Any(v => ManagedEffects.Value(v, Proven).InvalidatesMemory)) facts.Clear();
        switch (statement)
        {
            case ManagedAssignment assignment:
                var value = Closed(assignment.Value, facts);
                Kill(assignment.Target.Variable, facts);
                if (value is not null && !Mentions(value, assignment.Target.Variable)) facts[assignment.Target.Variable] = value;
                break;
            case ManagedStore { Target: FieldValue written }:
                foreach (var (variable, fact) in facts.ToArray())
                    if (ManagedValues.Walk(fact).OfType<FieldValue>().Any(f => ReferenceEquals(f.Field.Field, written.Field.Field))) facts.Remove(variable);
                break;
            case ManagedStore { Target: ArrayElementValue or StaticFieldValue }:
            case ManagedCheck or ManagedBranch or ManagedJump or ManagedSwitch or ManagedReturn or ManagedThrow:
                break;
            default:
                facts.Clear();
                break;
        }
    }

    private static Dictionary<Variable, ManagedValue> Across(ManagedEdge edge, Dictionary<Variable, ManagedValue> facts)
    {
        var result = new Dictionary<Variable, ManagedValue>(facts);
        var copies = edge.Copies.Select(c => (Target: c.Target.Variable, Value: Closed(c.Value, facts))).ToArray();
        foreach (var (target, _) in copies) Kill(target, result);
        foreach (var (target, value) in copies)
            if (value is not null && !copies.Any(c => Mentions(value, c.Target))) result[target] = value;
        return result;
    }

    private static bool Narrowed(Dictionary<Variable, ManagedValue> known, Dictionary<Variable, ManagedValue> arriving)
    {
        var changed = false;
        foreach (var (variable, fact) in known.ToArray())
            if (!arriving.TryGetValue(variable, out var other) || !other.Equals(fact))
            {
                known.Remove(variable);
                changed = true;
            }
        return changed;
    }

    /// <summary>值能写成字段读取时的形式；接收者只接受局部和形参。</summary>
    private static ManagedValue? Closed(ManagedValue value, Dictionary<Variable, ManagedValue> facts) => value switch
    {
        FieldValue { Receiver: LocalValue or ArgumentValue } field => new FieldValue(field.Receiver, field.Field, field.Type, field.Width),
        ArrayLengthValue { Array: LocalValue or ArgumentValue } or StringLengthValue { String: LocalValue or ArgumentValue } => value,
        LocalValue local => facts.GetValueOrDefault(local.Variable),
        ConversionValue conversion => Closed(conversion.Operand, facts) is { } operand ? conversion with { Operand = operand } : null,
        _ => null,
    };

    private static void Kill(Variable variable, Dictionary<Variable, ManagedValue> facts)
    {
        facts.Remove(variable);
        foreach (var (other, fact) in facts.ToArray())
            if (Mentions(fact, variable)) facts.Remove(other);
    }

    private static bool Mentions(ManagedValue value, Variable variable) =>
        ManagedValues.Walk(value).OfType<LocalValue>().Any(l => l.Variable.Equals(variable));
}
