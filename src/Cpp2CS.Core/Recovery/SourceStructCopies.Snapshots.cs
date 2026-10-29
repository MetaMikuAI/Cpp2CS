using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

internal static partial class SourceStructCopies
{
    /// <summary>连续读取完整结构体时保存整值，跨调用使用的叶子仍来自原位置的快照。</summary>
    internal static ManagedBody SnapshotReads(ManagedBody body)
    {
        static (ManagedValue Root, IReadOnlyList<FieldRef> Path)? ReadPath(ManagedValue value)
        {
            if (value is not ChoiceValue choice) return FieldPath(value);
            if (FieldPath(choice.True) is not { } first || FieldPath(choice.False) is not { } second
                || !first.Root.Type.Equals(second.Root.Type) || !first.Path.SequenceEqual(second.Path)
                || !ManagedValues.Walk(choice.Condition).All(v => v is LocalValue or ArgumentValue or ConstantValue
                    or ConversionValue or ComparisonValue or BooleanValue or NegatedValue)) return null;
            return (new ChoiceValue(choice.Condition, first.Root, second.Root, first.Root.Type, 0), first.Path);
        }
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<ManagedAssignment>().Select(a => a.Target.Variable)
            .Concat(statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.OfType<ManagedAwait>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable))
            .GroupBy(v => v).ToDictionary(g => g.Key, g => g.Count());
        var addressed = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>()
            .Select(l => l.Variable).ToHashSet();
        var next = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Where(l => l.Variable.Storage.Bank == Bank.Temp)
            .Select(l => l.Variable.Storage.Index).Concat(definitions.Keys.Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index))
            .DefaultIfEmpty(0).Max() + 1;
        var replacements = new Dictionary<Variable, ManagedValue>();
        var removed = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
        var starts = new Dictionary<ManagedStatement, ManagedAssignment>(ReferenceEqualityComparer.Instance);
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not ManagedAssignment first || ReadPath(first.Value) is not { } initial
                    || initial.Root is not (ArrayElementValue or FieldValue or ChoiceValue) || initial.Root.Type is not DefinitionRef type
                    || LeafPaths(type) is not { Count: > 1 } expected) continue;
                var reads = block.Statements.Skip(i).Take(expected.Count).OfType<ManagedAssignment>().ToArray();
                if (reads.Length != expected.Count || reads.Any(a => ReadPath(a.Value) is not { } path || !path.Root.Equals(initial.Root)
                    || definitions.GetValueOrDefault(a.Target.Variable) != 1 || addressed.Contains(a.Target.Variable)
                    || !a.Target.Type.Equals(a.Value.Type)
                    || ManagedValues.Walk(initial.Root).OfType<LocalValue>().Any(l => l.Variable == a.Target.Variable))
                    || !SamePaths(expected, reads.Select(a => ReadPath(a.Value)!.Value.Path))) continue;
                var snapshot = new LocalValue(new(Storage.Temp(next++), 1), type, 0);
                starts[first] = new(first.Address, snapshot, initial.Root);
                foreach (var read in reads)
                {
                    // 全部字段使用同一条件选择同布局来源时，只选择并快照一次整个结构体。
                    var leaf = read.Value is ChoiceValue choice ? choice.True : read.Value;
                    var root = FieldPath(leaf)!.Value.Root;
                    ManagedValue ReplaceRoot(ManagedValue value) => value.Equals(root) ? snapshot : ManagedValues.Map(value, ReplaceRoot);
                    replacements[read.Target.Variable] = ReplaceRoot(leaf);
                    removed.Add(read);
                }
                i += reads.Length - 1;
            }
        ManagedValue Replace(ManagedValue value) => value is LocalValue local && replacements.TryGetValue(local.Variable, out var field)
            ? field : ManagedValues.Map(value, Replace);
        if (replacements.Count != 0)
            body = body with { Blocks = body.Blocks.Select(block => block with { Statements = block.Statements.SelectMany(statement =>
                starts.TryGetValue(statement, out var snapshot) ? new ManagedStatement[] { snapshot with { Value = Replace(snapshot.Value) } }
                : removed.Contains(statement) ? [] : [ManagedValues.Map(statement, Replace, target => ManagedValues.Map(target, Replace))]).ToArray() }).ToArray() };
        return WholeSnapshotWrites(body);
    }

    private static ManagedBody WholeSnapshotWrites(ManagedBody body) => body with { Blocks = body.Blocks.Select(block =>
    {
        var statements = block.Statements.ToList();
        for (var i = 0; i < statements.Count; i++)
        {
            if (statements[i] is not ManagedStore first || FieldPath(first.Target, write: true) is not { } target
                || FieldPath(first.Value) is not { Root: LocalValue or ArgumentValue } source || !source.Root.Type.Equals(target.Root.Type)
                || source.Root.Type is not DefinitionRef type || LeafPaths(type) is not { Count: > 1 } expected) continue;
            var writes = statements.Skip(i).Take(expected.Count).OfType<ManagedStore>().ToArray();
            if (writes.Length != expected.Count || writes.Any(s => FieldPath(s.Target, write: true) is not { } to
                || !to.Root.Equals(target.Root) || FieldPath(s.Value) is not { } from || !from.Root.Equals(source.Root)
                || !to.Path.SequenceEqual(from.Path) || !s.Target.Type.Equals(s.Value.Type))
                || !SamePaths(expected, writes.Select(s => FieldPath(s.Target, write: true)!.Value.Path))) continue;
            statements.RemoveRange(i, writes.Length);
            statements.Insert(i, target.Root is LocalValue local ? new ManagedAssignment(first.Address, local, source.Root)
                : new ManagedStore(first.Address, target.Root, source.Root));
        }
        return block with { Statements = statements };
    }).ToArray() };
}
