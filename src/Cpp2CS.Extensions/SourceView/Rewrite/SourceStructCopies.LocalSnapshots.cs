using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

internal static partial class SourceStructCopies
{
    // 嵌套字段经临时结构体拆开后仍可完整复制；无关常量赋值保持原位置。
    private static ManagedBody LocalSnapshotCopies(ManagedBody body)
    {
        var uses = body.Blocks.SelectMany(b => b.Statements).SelectMany(s =>
                (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
        static ManagedValue NativeRead(ManagedValue value) => ManagedValues.Map(value is FieldValue field
            && field.Accessor is { Write: false } accessor && accessor.Field.Equals(field.Field)
            && accessor.ValueType.Equals(field.Type) && accessor.Width == field.Width ? field with { Accessor = null } : value, NativeRead);
        return body with
        {
            Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToList();
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment first || FieldPath(NativeRead(first.Value)) is not { Root: LocalValue source }
                    || source.Type is not DefinitionRef type || LeafPaths(type) is not { Count: > 1 } expected) continue;
                var reads = new Dictionary<Variable, ManagedValue>();
                var removed = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
                var end = i;
                ManagedValue Expand(ManagedValue value) => value is LocalValue local && reads.TryGetValue(local.Variable, out var expanded)
                    ? expanded : ManagedValues.Map(value, Expand);
                while (end < statements.Count && statements[end] is ManagedAssignment read
                    && read.Target.Variable != source.Variable && !reads.ContainsKey(read.Target.Variable))
                {
                    var value = Expand(NativeRead(read.Value));
                    if (FieldPath(value) is { } path && path.Root.Equals(source) && read.Target.Type.Equals(value.Type)
                        && expected.Any(p => p.Take(path.Path.Count).SequenceEqual(path.Path)))
                    { reads.Add(read.Target.Variable, value); removed.Add(read); }
                    else if (read.Value is not ConstantValue) break;
                    end++;
                }
                var firstWrite = end;
                var paths = new List<IReadOnlyList<FieldRef>>();
                LocalValue? destination = null;
                while (end < statements.Count && statements[end] is ManagedStore write
                    && FieldPath(write.Target, write: true) is { Root: LocalValue target } to
                    && target.Type.Equals(type) && (destination is null || destination.Equals(target))
                    && write.Value is LocalValue copied && reads.TryGetValue(copied.Variable, out var value)
                    && FieldPath(value) is { } from && from.Root.Equals(source) && to.Path.SequenceEqual(from.Path)
                    && write.Target.Type.Equals(value.Type) && !paths.Any(p => p.SequenceEqual(to.Path)))
                {
                    destination = target;
                    paths.Add(to.Path);
                    removed.Add(write);
                    end++;
                }
                if (destination is null || !SamePaths(expected, paths)) continue;
                var consumed = removed.SelectMany(s => s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s))
                    .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
                if (reads.Keys.Any(v => consumed.GetValueOrDefault(v) != uses.GetValueOrDefault(v))) continue;
                var replacement = statements.Skip(i).Take(end - i).Where(s => !removed.Contains(s)).ToList();
                replacement.Add(new ManagedAssignment(statements[firstWrite].Address, destination, source));
                statements.RemoveRange(i, end - i);
                statements.InsertRange(i, replacement);
                i += replacement.Count - 1;
            }
            return block with { Statements = statements };
        }).ToArray()
        };
    }
}
