using Cpp2CS.Recovery.Effects;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    private static IEnumerable<ManagedValue> ReadValues(ManagedStatement statement) =>
        (statement is ManagedAssignment assignment ? [assignment.Value] : ManagedValues.Of(statement))
        .Concat(ManagedValues.CopiedValues(statement));

    /// <summary>区域内写入同一稳定值的局部副本：旧值在入口已死或已等于该值，故可提前保存。</summary>
    private IReadOnlyList<ManagedAssignment> InlineCopies(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks,
        ulong startBlock, int start, InlineMatch match, IReadOnlySet<Variable> escaping, ManagedValue? self)
    {
        var statements = match.Covered.Select(p => blocks[p.Block].Statements[p.Index]).ToArray();
        var edgeTargets = statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable).ToHashSet();
        var addressed = body.Blocks.SelectMany(b => b.Statements).SelectMany(ReadValues).SelectMany(ManagedValues.Walk)
            .OfType<AddressValue>().SelectMany(a => ManagedValues.Walk(a.Target)).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var copies = new List<ManagedAssignment>();
        bool Stable(ManagedValue value) => StableInRegion(value, match, edgeTargets, addressed);
        foreach (var variable in escaping)
        {
            if (edgeTargets.Contains(variable) || addressed.Contains(variable)) continue;
            var writes = statements.OfType<ManagedAssignment>().Where(a => a.Target.Variable == variable).ToArray();
            if (writes.Length == 0 || statements.OfType<ManagedCall>().Any(c => c.Result?.Variable == variable)) continue;
            var value = writes[0].Value;
            // 夹在区域里的调用方读取，发生在第一个效果之前：提到调用之前读到的是同一个值。
            if (writes.Length == 1 && match.Defined.GetValueOrDefault(variable) is Observed early && match.EarlyReads.Contains(early)
                && !LiveAt(body, blocks, startBlock, start, variable) && Materialize(early, self, writes[0].Address, match) is { } read)
            {
                copies.Add(writes[0] with { Address = blocks[startBlock].Statements[start].Address, Value = read });
                continue;
            }
            if (!Stable(value) || writes.Any(a => a.Value != value)) continue;
            if (LiveAt(body, blocks, startBlock, start, variable)
                && !match.Inputs.Any(input => input.Local.Variable == variable && SameTerm(input.Value, value))
                && !SameCopyAt(body, blocks, startBlock, start, variable, value)) continue;
            copies.Add(writes[0] with { Address = blocks[startBlock].Statements[start].Address });
        }
        return copies;
    }

    /// <summary>
    /// 区域内异常边 φ 的赋值提到调用之前：这些局部只在异常到达时读取，每个抛出点之前都会重新赋值，
    /// 调用不抛出的路径上多写一次观察不到。同一局部须在区域内取同一个、不受区域影响的值，否则调用抛出时值不对。
    /// </summary>
    private IReadOnlyList<ManagedAssignment>? ArrivalCopies(ManagedBody body, InlineMatch match, IReadOnlyDictionary<ulong, ManagedBlock> blocks, ulong at, out string failure)
    {
        failure = "异常到达的赋值不能提前";
        if (match.Arrivals.Count == 0) return [];
        var statements = match.Covered.Select(p => blocks[p.Block].Statements[p.Index]).ToArray();
        var edgeTargets = statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable).ToHashSet();
        var addressed = body.Blocks.SelectMany(b => b.Statements).SelectMany(ReadValues).SelectMany(ManagedValues.Walk)
            .OfType<AddressValue>().SelectMany(a => ManagedValues.Walk(a.Target)).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var copies = new List<ManagedAssignment>();
        foreach (var group in match.Arrivals.GroupBy(a => a.Target.Variable))
        {
            var value = group.First().Value;
            if (group.Any(a => !SameTerm(a.Value, value))) { failure = $"{group.Key} 在区域内各抛出点的值不同"; return null; }
            if (!StableInRegion(value, match, edgeTargets, addressed)) { failure = $"{group.Key} 的值依赖区域内的结果"; return null; }
            copies.Add(group.First() with { Address = at });
        }
        return copies;
    }

    /// <summary>值在整个区域内不变：只依赖常量、形参和区域内没有写入、也没有被取址的局部。</summary>
    private static bool StableInRegion(ManagedValue value, InlineMatch match, IReadOnlySet<Variable> edgeTargets, IReadOnlySet<Variable> addressed) => value switch
    {
        ConstantValue or ArgumentValue => true,
        LocalValue source => !match.Defined.ContainsKey(source.Variable) && !edgeTargets.Contains(source.Variable) && !addressed.Contains(source.Variable),
        ComparisonValue or NegatedValue or BooleanValue => ManagedValues.Children(value).All(v => StableInRegion(v, match, edgeTargets, addressed)),
        BinaryValue { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr }
            => ManagedValues.Children(value).All(v => StableInRegion(v, match, edgeTargets, addressed)),
        ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion => StableInRegion(conversion.Operand, match, edgeTargets, addressed),
        _ => false,
    };

    /// <summary>
    /// 局部在给定位置是否一定持有 value：沿全部入边查找最近赋值，局部之间的复制继续追溯；未取址的局部可跨调用保值，
    /// value 的输入被改写或遇到异常入口时不成立。环上按归纳假设成立：循环不变量由其他入边保证，只要有一条入边不成立结论就是否定。
    /// </summary>
    private bool SameCopyAt(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks,
        ulong block, int index, Variable target, ManagedValue value)
    {
        var inputs = ManagedValues.Walk(value).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var active = new HashSet<(Variable, ulong, int)>();
        var known = new Dictionary<(Variable, ulong, int), bool>();
        bool Visit(Variable holder, ulong at, int before)
        {
            var point = (holder, at, before);
            if (known.TryGetValue(point, out var result)) return result;
            if (!active.Add(point)) return true;
            result = Check(holder, at, before);
            active.Remove(point);
            return known[point] = result;
        }
        bool Holds(ManagedValue source, ulong at, int before) => source is LocalValue local && !SameTerm(source, value)
            ? Visit(local.Variable, at, before) : SameTerm(source, value);
        bool Check(Variable holder, ulong at, int before)
        {
            for (var i = before - 1; i >= 0; i--)
            {
                var statement = blocks[at].Statements[i];
                var written = statement switch { ManagedAssignment a => a.Target.Variable, ManagedCall c => c.Result?.Variable, _ => null };
                if (written is not null && inputs.Contains(written)) return false;
                if (written == holder) return statement is ManagedAssignment assignment && Holds(assignment.Value, at, i);
            }
            if (at == body.Blocks[0].Address || body.Regions.Any(r => r.HandlerEntry == at)) return false;
            var incoming = blocks.Values.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges)
                .Where(e => e.Target == at).Select(e => (Block: b, Edge: e))).ToArray();
            return incoming.Length > 0 && incoming.All(p =>
            {
                if (p.Edge.Copies.Any(c => inputs.Contains(c.Target.Variable))) return false;
                var end = blocks[p.Block.Address].Statements.Count;
                return p.Edge.Copies.FirstOrDefault(c => c.Target.Variable == holder) is { } copy
                    ? Holds(copy.Value, p.Block.Address, end) : Visit(holder, p.Block.Address, end);
            });
        }
        return Visit(target, block, index);
    }

    /// <summary>数组一经创建长度不变，形参不被改写，它的长度在方法内是同一个值。</summary>
    private static bool ImmutableValue(ManagedValue value) => value is ArrayLengthValue { Array: ArgumentValue };

    /// <summary>从指定位置出发，在覆盖写入前是否可能读取旧值；包括异常出边及边上的并行复制。</summary>
    private bool LiveAt(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks, ulong block, int index, Variable variable)
    {
        var work = new Stack<(ulong Block, int Index)>();
        var seen = new HashSet<(ulong Block, int Index)>();
        work.Push((block, index));
        while (work.TryPop(out var point))
        {
            if (!seen.Add(point)) continue;
            var statements = blocks[point.Block].Statements;
            for (var i = point.Index; i < statements.Count; i++)
            {
                var statement = statements[i];
                var reads = ReadValues(statement).ToArray();
                if (reads.SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => l.Variable == variable)) return true;
                if (statement is ManagedCall or ManagedCheck or ManagedThrow or ManagedRethrow
                    || reads.Any(v => !NonThrowingInlineValue(v)))
                    foreach (var region in body.Regions.Where(r => r.Try.Contains(point.Block)))
                        work.Push((region.HandlerEntry, 0));
                if (statement is ManagedAssignment a && a.Target.Variable == variable
                    || statement is ManagedCall c && c.Result?.Variable == variable) break;
                foreach (var edge in ManagedValues.Edges(statement))
                    if (!edge.Copies.Any(c => c.Target.Variable == variable)) work.Push((edge.Target, 0));
            }
        }
        return false;
    }

    private bool NonThrowingInlineValue(ManagedValue value) => InlineEffects(value).CanDiscard;

    private EffectSummary InlineEffects(ManagedValue value) => ManagedEffects.Value(value, v => v switch
    {
        Returned => EffectSummary.None,
        Observed observed => InlineEffects(observed.Read),
        NewObjectValue { Transparent: true, Type: DefinitionRef { Definition.IsValueType: true } structure } construction
            when NonThrowingConstructor(construction.Constructor, structure)
            => construction.Arguments.Aggregate(EffectSummary.None, (effect, argument) => effect | InlineEffects(argument)),
        _ => null,
    });

    private readonly Dictionary<MethodRef, bool> nonThrowingConstructors = [];

    private bool NonThrowingConstructor(MethodRef method, DefinitionRef structure)
    {
        if (nonThrowingConstructors.TryGetValue(method, out var known)) return known;
        nonThrowingConstructors[method] = false;
        return nonThrowingConstructors[method] = summaries(method) is { Body: { Regions.Count: 0 } template }
            && ConstructorWrites(template, structure) is { } writes
            && writes.All(w => w.Value is ConstantValue or ArgumentValue or IndirectValue { Address: ArgumentValue { Type: ByRefRef } })
            && template.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
                .All(a => a.Value is IndirectValue { Address: ArgumentValue { Type: ByRefRef } } || NonThrowingInlineValue(a.Value));
    }
}
