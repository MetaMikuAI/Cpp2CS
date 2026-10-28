using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

internal static partial class SourceListCalls
{
    // 为共用快速写入尾部建立独占视图，只有完整 Add 模式通过后才采用。
    private static ManagedBody? MatchSharedAdd(ManagedBody body, ManagedTypes types, Action<ulong, MethodRef> matched,
        Func<MethodRef, SourceValueConstructor?>? constructor)
    {
        var list = types.CorlibDefinition("System.Collections.Generic.List");
        if (list is null) return null;
        var flow = new PatternFlow(body);
        var next = body.Blocks.Max(b => b.Address) + 1;
        foreach (var source in body.Blocks)
        for (var start = 0; start < source.Statements.Count; start++)
        {
            if (source.Statements[start] is not ManagedAssignment first || Strip(first.Value) is not FieldValue field
                || field.Field.Field.Owner != list || field.Field.Field.Name is not ("_items" or "_version")
                || flow.Straight(source.Address, start, source.Address).OfType<ManagedBranch>().FirstOrDefault() is not { } branch) continue;
            foreach (var edge in ManagedValues.Edges(branch))
            {
                if (edge.Copies.Count == 0 || edge.Copies.Select(c => c.Target.Variable).Distinct().Count() != edge.Copies.Count
                    || edge.Copies.Any(c => c.Value is not (LocalValue or ArgumentValue or ConstantValue))
                    || body.Regions.Any(r => r.Handler.Contains(edge.Target))
                    || body.Blocks.FirstOrDefault(b => b.Address == edge.Target) is not { } tail
                    || tail.Statements is not [ManagedStore { Target: FieldValue size }, ManagedStore { Target: ArrayElementValue }, ManagedJump]
                    || size.Field.Field.Owner != list || size.Field.Field.Name != "_size") continue;
                var values = edge.Copies.ToDictionary(c => c.Target.Variable, c => c.Value);
                if (body.Blocks.Where(b => b != tail).SelectMany(b => b.Statements)
                    .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                    .OfType<LocalValue>().Any(l => values.ContainsKey(l.Variable))) continue;
                ManagedValue Replace(ManagedValue value) => value is LocalValue local && values.TryGetValue(local.Variable, out var input)
                    ? input : ManagedValues.Map(value, Replace);
                var clone = new ManagedBlock(next, tail.Statements.Select(s => ManagedValues.Map(s, Replace)).ToArray());
                var replacement = ManagedValues.MapEdges(branch, original => ReferenceEquals(original, edge) ? new(next, []) : original);
                var view = body with
                {
                    Blocks = body.Blocks.SelectMany(block => block == tail ? new[] { clone, block }
                        : [block with { Statements = block.Statements.Select(s => ReferenceEquals(s, branch) ? replacement : s).ToArray() }]).ToArray(),
                    Regions = body.Regions.Select(r => r with
                    { Try = r.Try.SelectMany(address => address == tail.Address ? new[] { next, address } : [address]).ToArray() }).ToArray(),
                };
                if (MatchAdd(view, types, matched, constructor, first) is { } result) return result;
            }
        }
        return null;
    }
}
