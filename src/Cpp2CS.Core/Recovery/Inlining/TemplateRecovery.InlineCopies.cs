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
                && !match.Inputs.Any(input => input.Local.Variable == variable && SameTerm(input.Value, value))) continue;
            copies.Add(writes[0] with { Address = blocks[startBlock].Statements[start].Address });
        }
        return copies;
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

    private bool NonThrowingInlineValue(ManagedValue value) => value switch
    {
        LocalValue or ArgumentValue or ConstantValue => true,
        Returned => true,
        Observed observed => NonThrowingInlineValue(observed.Read),
        AddressValue { Target: LocalValue } => true,
        IndirectValue { Address: AddressValue { Target: LocalValue } } => true,
        FieldValue field when field.Receiver.Type is DefinitionRef { Definition.IsValueType: true }
            or ByRefRef { Element: DefinitionRef { Definition.IsValueType: true } }
            => NonThrowingInlineValue(field.Receiver),
        ComparisonValue or NegatedValue or BooleanValue => ManagedValues.Children(value).All(NonThrowingInlineValue),
        ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion => NonThrowingInlineValue(conversion.Operand),
        ComposedValue composed => composed.Leaves.All(l => NonThrowingInlineValue(l.Value)),
        NewObjectValue { Transparent: true, Type: DefinitionRef { Definition.IsValueType: true } structure } construction
            => NonThrowingConstructor(construction.Constructor, structure) && construction.Arguments.All(NonThrowingInlineValue),
        _ => false,
    };

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
