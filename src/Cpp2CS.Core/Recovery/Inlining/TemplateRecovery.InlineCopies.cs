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
        ulong startBlock, int start, InlineMatch match, IReadOnlySet<Variable> escaping)
    {
        var statements = match.Covered.Select(p => blocks[p.Block].Statements[p.Index]).ToArray();
        var edgeTargets = statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable).ToHashSet();
        var addressed = body.Blocks.SelectMany(b => b.Statements).SelectMany(ReadValues).SelectMany(ManagedValues.Walk)
            .OfType<AddressValue>().SelectMany(a => ManagedValues.Walk(a.Target)).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var copies = new List<ManagedAssignment>();
        bool Stable(ManagedValue value) => value switch
        {
            ConstantValue or ArgumentValue => true,
            LocalValue source => !match.Defined.ContainsKey(source.Variable) && !edgeTargets.Contains(source.Variable) && !addressed.Contains(source.Variable),
            ComparisonValue or NegatedValue or BooleanValue => ManagedValues.Children(value).All(Stable),
            BinaryValue { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr }
                => ManagedValues.Children(value).All(Stable),
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion => Stable(conversion.Operand),
            _ => false,
        };
        foreach (var variable in escaping)
        {
            if (edgeTargets.Contains(variable) || addressed.Contains(variable)) continue;
            var writes = statements.OfType<ManagedAssignment>().Where(a => a.Target.Variable == variable).ToArray();
            if (writes.Length == 0 || statements.OfType<ManagedCall>().Any(c => c.Result?.Variable == variable)) continue;
            var value = writes[0].Value;
            if (!Stable(value) || writes.Any(a => a.Value != value)) continue;
            if (LiveAt(body, blocks, startBlock, start, variable)
                && !match.Inputs.Any(input => input.Local.Variable == variable && SameTerm(input.Value, value))
                && !SameCopyAt(body, blocks, startBlock, start, variable, value)) continue;
            copies.Add(writes[0] with { Address = blocks[startBlock].Statements[start].Address });
        }
        return copies;
    }

    /// <summary>沿全部入边查找最近赋值；未取址的局部可跨调用保值，表达式输入被改写或遇到异常入口时停止证明。</summary>
    private bool SameCopyAt(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks,
        ulong block, int index, Variable target, ManagedValue value)
    {
        var inputs = ManagedValues.Walk(value).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var active = new HashSet<(ulong, int)>();
        var known = new Dictionary<(ulong, int), bool>();
        bool Visit(ulong at, int before)
        {
            var point = (at, before);
            if (known.TryGetValue(point, out var result)) return result;
            if (!active.Add(point)) return false;
            result = Check(at, before);
            active.Remove(point);
            return known[point] = result;
        }
        bool Check(ulong at, int before)
        {
            for (var i = before - 1; i >= 0; i--)
            {
                var statement = blocks[at].Statements[i];
                var written = statement switch { ManagedAssignment a => a.Target.Variable, ManagedCall c => c.Result?.Variable, _ => null };
                if (written is not null && inputs.Contains(written)) return false;
                if (written == target) return statement is ManagedAssignment assignment && SameTerm(assignment.Value, value);
            }
            if (at == body.Blocks[0].Address || body.Regions.Any(r => r.HandlerEntry == at)) return false;
            var incoming = blocks.Values.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges)
                .Where(e => e.Target == at).Select(e => (Block: b, Edge: e))).ToArray();
            return incoming.Length > 0 && incoming.All(p =>
            {
                if (p.Edge.Copies.Any(c => inputs.Contains(c.Target.Variable))) return false;
                if (p.Edge.Copies.FirstOrDefault(c => c.Target.Variable == target) is { } copy)
                    return SameTerm(copy.Value, value);
                return Visit(p.Block.Address, p.Block.Statements.Count);
            });
        }
        return Visit(block, index);
    }

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
