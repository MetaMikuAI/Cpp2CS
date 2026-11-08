using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 局部变量此刻等于哪个字段的内容或数组、字符串的长度（前向必达数据流）：v = r.f 之后，到 v、r 被改写或这个字段可能被写之前，v 就是 r.f 的当前值。
/// 编译器复用较早的读取、在不改内存的路径上省掉重读时，内联副本里看不到这次读取，比较要靠这个事实。
/// 另记录字段此刻的已知常量内容（写入常量之后，或被调用的方法在每条返回路径上都写同一常量）：局部被赋予同一常量时，它就是这个字段的当前值。
/// 调用、未知写入和可能运行类构造的访问都清空事实（调用另按方法体的必然写入补回已知内容）；处理块入口没有事实。
/// </summary>
internal sealed class AvailableFields
{
    private readonly Dictionary<ulong, ManagedBlock> blocks;
    private readonly Dictionary<ulong, State> entries = [];
    private readonly Func<ManagedInvocation, CallSummary?> callEffects;


    /// <summary>变量与字段读取的等价事实，以及字段的已知常量内容。</summary>
    private sealed class State
    {
        public Dictionary<Variable, ManagedValue> Vars { get; init; } = [];
        public Dictionary<(ManagedValue Receiver, FieldDef Field), (FieldValue Location, ConstantValue Value)> Known { get; init; } = [];
        /// <summary>字段此刻持有的形参或局部（存入之后）。</summary>
        public Dictionary<(ManagedValue Receiver, FieldDef Field), (FieldValue Location, ManagedValue Value)> Held { get; init; } = [];
        public State Copy() => new() { Vars = new(Vars), Known = new(Known), Held = new(Held) };
        public void Clear() { Vars.Clear(); Known.Clear(); Held.Clear(); }
    }

    public AvailableFields(ManagedBody body, Func<ManagedInvocation, CallSummary?> callEffects)
    {
        this.callEffects = callEffects;
        blocks = body.Blocks.ToDictionary(b => b.Address);
        // 内联证明可能已经删掉了处理块，区域信息里的入口不一定还在。
        var handlers = body.Regions.Select(r => r.HandlerEntry).Where(blocks.ContainsKey).ToHashSet();
        var pending = new Queue<ulong>();
        foreach (var start in handlers.Prepend(body.Blocks[0].Address).Distinct())
        {
            entries[start] = new();
            pending.Enqueue(start);
        }
        while (pending.TryDequeue(out var address))
        {
            var facts = entries[address].Copy();
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
        var facts = entry.Copy();
        foreach (var statement in blocks[block].Statements.Take(index)) Apply(statement, facts);
        return facts.Vars;
    }

    /// <summary>
    /// 第 index 条语句之前字段的已知内容：存入的形参或局部、已知的常量，或调用前的值经调用加上常量。
    /// 到字段可能被写、该值被改写之前，读这个字段得到的就是它。
    /// </summary>
    public IReadOnlyList<(FieldValue Location, ManagedValue Value)> HeldAt(ulong block, int index)
    {
        if (!entries.TryGetValue(block, out var entry)) return [];
        var facts = entry.Copy();
        foreach (var statement in blocks[block].Statements.Take(index)) Apply(statement, facts);
        return [.. facts.Held.Values, .. facts.Known.Values.Where(k => k.Value.Width == k.Location.Width).Select(k => (k.Location, (ManagedValue)k.Value))];
    }

    private void Apply(ManagedStatement statement, State facts)
    {
        // 证明过的访问器只读一个字段，调用它不改内存。
        static EffectSummary? Proven(ManagedValue value) => value is FieldValue { Accessor: not null } access ? ManagedEffects.Value(access.Receiver) : null;
        if (ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Any(v => ManagedEffects.Value(v, Proven).InvalidatesMemory))
            facts.Clear();
        switch (statement)
        {
            // 方法体已知时，调用只使它可能写的字段上的事实失效，并留下每条返回路径上都成立的常量写入。
            case ManagedCall { Invocation: var invocation } call when callEffects(invocation) is { } effect:
                var advanced = Advanced(effect, facts);
                foreach (var (variable, fact) in facts.Vars.ToArray())
                    if (ManagedValues.Walk(fact).OfType<FieldValue>().Any(f => effect.Writes.Any(w => HeapAlias.MayShare(f.Field, w)))) facts.Vars.Remove(variable);
                foreach (var key in facts.Known.Keys.ToArray())
                    if (effect.Writes.Any(w => HeapAlias.MayShare(facts.Known[key].Location.Field, w))) facts.Known.Remove(key);
                foreach (var key in facts.Held.Keys.ToArray())
                    if (effect.Writes.Any(w => HeapAlias.MayShare(facts.Held[key].Location.Field, w))) facts.Held.Remove(key);
                if (call.Result is { } result) Kill(result.Variable, facts);
                foreach (var (location, stored) in effect.Stores)
                    if (Rooted(location.Receiver)) facts.Known[(location.Receiver, location.Field.Field)] = (location, stored);
                foreach (var (location, content) in advanced)
                {
                    if (content is ConstantValue known) facts.Known[(location.Receiver, location.Field.Field)] = (location, known);
                    else if (call.Result is not { } returned || !Mentions(content, returned.Variable)) facts.Held[(location.Receiver, location.Field.Field)] = (location, content);
                }
                break;
            case ManagedAssignment assignment:
                var value = Closed(assignment.Value, facts);
                Kill(assignment.Target.Variable, facts);
                if (value is not null && !Mentions(value, assignment.Target.Variable)) facts.Vars[assignment.Target.Variable] = value;
                break;
            case ManagedStore { Target: FieldValue written } store:
                foreach (var (variable, fact) in facts.Vars.ToArray())
                    if (ManagedValues.Walk(fact).OfType<FieldValue>().Any(f => HeapAlias.MayShare(f.Field, written.Field))) facts.Vars.Remove(variable);
                foreach (var key in facts.Known.Keys.ToArray())
                    if (HeapAlias.MayShare(facts.Known[key].Location.Field, written.Field)) facts.Known.Remove(key);
                foreach (var key in facts.Held.Keys.ToArray())
                    if (HeapAlias.MayShare(facts.Held[key].Location.Field, written.Field)) facts.Held.Remove(key);
                if (store.Value is ArgumentValue or LocalValue && Rooted(written.Receiver) && written.Width == store.Value.Width
                    && !(store.Value is LocalValue self && Mentions(written, self.Variable)))
                    facts.Held[(written.Receiver, written.Field.Field)] = (Plain(written), store.Value);
                if (store.Value is ConstantValue constant && Rooted(written.Receiver))
                    facts.Known[(written.Receiver, written.Field.Field)] = (new FieldValue(written.Receiver, written.Field, written.Type, written.Width), constant);
                break;
            case ManagedStore { Target: ArgumentValue written }:
                foreach (var (variable, fact) in facts.Vars.ToArray())
                    if (ManagedValues.Walk(fact).OfType<ArgumentValue>().Any(a => a.Index == written.Index)) facts.Vars.Remove(variable);
                foreach (var (key, held) in facts.Held.ToArray())
                    if (ManagedValues.Walk(held.Value).Concat(ManagedValues.Walk(held.Location)).OfType<ArgumentValue>().Any(a => a.Index == written.Index)) facts.Held.Remove(key);
                break;
            case ManagedStore { Target: ArrayElementValue or StaticFieldValue }:
            case ManagedCheck or ManagedBranch or ManagedJump or ManagedSwitch or ManagedReturn or ManagedThrow:
                break;
            default:
                facts.Clear();
                break;
        }
    }


    /// <summary>
    /// 调用把字段加上常量（<see cref="CallSummary.Increments"/>）时，调用之后的内容：调用前已知的常量、持有的值或读入的局部加上这个常量。
    /// </summary>
    private static List<(FieldValue Location, ManagedValue Value)> Advanced(CallSummary effect, State facts)
    {
        var result = new List<(FieldValue, ManagedValue)>();
        foreach (var (location, step) in effect.Increments)
        {
            if (!Rooted(location.Receiver)) continue;
            var key = (location.Receiver, location.Field.Field);
            var plain = Plain(location);
            ManagedValue? before = facts.Known.TryGetValue(key, out var known) && known.Value.Width == location.Width ? known.Value
                : facts.Held.TryGetValue(key, out var held) ? held.Value
                : facts.Vars.Where(v => v.Value.Equals(plain)).Select(v => new LocalValue(v.Key, location.Type, location.Width)).FirstOrDefault();
            if (before is not null) result.Add((plain, Plus(before, step)));
        }
        return result;
    }

    /// <summary>值加常量（按宽度取模）；常量与已有的加常量合并。</summary>
    private static ManagedValue Plus(ManagedValue value, ConstantValue step)
    {
        ulong Sum(ulong a) => (a + step.Bits) & Expr.Mask(value.Width);
        return value switch
        {
            ConstantValue constant => constant with { Bits = Sum(constant.Bits) },
            BinaryValue { Op: BinOp.Add, Right: ConstantValue inner } add when Sum(inner.Bits) == 0 => add.Left,
            BinaryValue { Op: BinOp.Add, Right: ConstantValue inner } add => add with { Right = inner with { Bits = Sum(inner.Bits) } },
            _ => new BinaryValue(BinOp.Add, value, step with { Type = value.Type }, value.Type, value.Width),
        };
    }

    /// <summary>
    /// 边上的复制是并行的：到达后目标持有来源原来的值。同一条边把局部 s 复制给 t 时，复制值的事实里的 s 写成 t，
    /// 循环头上接收者和它的字段读取一起成为 φ 时（v = r.f 与 r 各自经边复制），各入边的事实才能一致。
    /// </summary>
    private static State Across(ManagedEdge edge, State facts)
    {
        var result = facts.Copy();
        var renamed = new Dictionary<Variable, LocalValue>();
        foreach (var copy in edge.Copies)
            if (copy.Value is LocalValue source && source.Type.Equals(copy.Target.Type) && source.Width == copy.Target.Width)
                renamed.TryAdd(source.Variable, copy.Target);
        var targets = edge.Copies.Select(c => c.Target.Variable).ToHashSet();
        var copies = edge.Copies.Select(c => (Target: c.Target.Variable, Value: Closed(c.Value, facts) is { } closed ? Renamed(closed, renamed, targets) : null)).ToArray();
        foreach (var (target, _) in copies) Kill(target, result);
        foreach (var (target, value) in copies)
            if (value is not null) result.Vars[target] = value;
        return result;
    }

    /// <summary>事实里经边复制的局部换成复制目标；仍提到其他被改写的目标时不成立。</summary>
    private static ManagedValue? Renamed(ManagedValue value, IReadOnlyDictionary<Variable, LocalValue> renamed, IReadOnlySet<Variable> targets)
    {
        var failed = false;
        var mapped = ManagedValues.Map(value, child => Rename(child));
        ManagedValue Rename(ManagedValue child)
        {
            if (child is LocalValue local)
            {
                if (renamed.TryGetValue(local.Variable, out var target)) return target;
                failed |= targets.Contains(local.Variable);
                return child;
            }
            return ManagedValues.Map(child, Rename);
        }
        if (value is LocalValue whole) mapped = Rename(whole);
        return failed ? null : mapped;
    }

    private static bool Narrowed(State known, State arriving)
    {
        var changed = false;
        foreach (var (key, fact) in known.Held.ToArray())
            if (!arriving.Held.TryGetValue(key, out var other) || !other.Value.Equals(fact.Value))
            {
                known.Held.Remove(key);
                changed = true;
            }
        foreach (var (variable, fact) in known.Vars.ToArray())
            if (!arriving.Vars.TryGetValue(variable, out var other) || !other.Equals(fact))
            {
                known.Vars.Remove(variable);
                changed = true;
            }
        foreach (var (key, fact) in known.Known.ToArray())
            if (!arriving.Known.TryGetValue(key, out var other) || !other.Value.Equals(fact.Value))
            {
                known.Known.Remove(key);
                changed = true;
            }
        return changed;
    }

    /// <summary>值能写成字段读取时的形式；接收者只接受局部、形参和其上的字段链。常量取内容恰为它的字段。</summary>
    private static ManagedValue? Closed(ManagedValue value, State facts) => value switch
    {
        FieldValue field when Rooted(field.Receiver) => Plain(field),
        ArrayLengthValue { Array: LocalValue or ArgumentValue } or StringLengthValue { String: LocalValue or ArgumentValue } => value,
        LocalValue local => facts.Vars.GetValueOrDefault(local.Variable),
        ConversionValue conversion => Closed(conversion.Operand, facts) is { } operand ? conversion with { Operand = operand } : null,
        ConstantValue constant => FieldHolding(constant, facts),
        _ => null,
    };

    /// <summary>
    /// 内容恰为这个常量的字段；字段更窄时，常量是它零扩展（非负）或符号扩展（负）的结果，写成对应的转换。
    /// </summary>
    private static ManagedValue? FieldHolding(ConstantValue constant, State facts)
    {
        foreach (var (location, stored) in facts.Known.Values)
        {
            if (stored.Equals(constant)) return location;
            if (stored.Width >= constant.Width || stored.Width > 32 || constant.Width > 64) continue;
            var narrow = stored.Bits & ((1UL << stored.Width) - 1);
            var negative = (narrow >> (stored.Width - 1)) != 0;
            if (!negative && constant.Bits == narrow) return new ConversionValue(ConvKind.ZeroExtend, location, constant.Type, constant.Width);
            var widened = constant.Width == 64 ? narrow | ~((1UL << stored.Width) - 1) : (narrow | ~((1UL << stored.Width) - 1)) & ((1UL << constant.Width) - 1);
            if (negative && constant.Bits == widened) return new ConversionValue(ConvKind.SignExtend, location, constant.Type, constant.Width);
        }
        return null;
    }

    /// <summary>字段链只保留位置：去掉各层读取上的访问器与待证标记，与调用方自己读出的形式一致。</summary>
    private static FieldValue Plain(FieldValue field) =>
        new(field.Receiver is FieldValue inner ? Plain(inner) : field.Receiver, field.Field, field.Type, field.Width);

    /// <summary>接收者是局部或形参，或其上的字段链（如枚举器局部的当前元素字段）；任何对链上字段的写入都会使事实失效。</summary>
    private static bool Rooted(ManagedValue receiver) => receiver is LocalValue or ArgumentValue || receiver is FieldValue { Receiver: var inner } && Rooted(inner);

    private static void Kill(Variable variable, State facts)
    {
        facts.Vars.Remove(variable);
        foreach (var (other, fact) in facts.Vars.ToArray())
            if (Mentions(fact, variable)) facts.Vars.Remove(other);
        foreach (var (key, fact) in facts.Known.ToArray())
            if (Mentions(fact.Location, variable)) facts.Known.Remove(key);
        foreach (var (key, held) in facts.Held.ToArray())
            if (Mentions(held.Location, variable) || Mentions(held.Value, variable)) facts.Held.Remove(key);
    }

    private static bool Mentions(ManagedValue value, Variable variable) =>
        ManagedValues.Walk(value).OfType<LocalValue>().Any(l => l.Variable.Equals(variable));
}
