using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

internal static partial class SourceStructCopies
{
    // 构造入口只写自身常量字段时，交错的结构体叶子可合成完整初始化器；不跨读取、调用或分支。
    private static ManagedBody ConstructorConstants(ManagedBody body)
    {
        if (body.Method?.Method is not { Name: ".ctor", IsStatic: false } method || body.Blocks.Count == 0
            || method.Owner.IsValueType || (method.Owner.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout) return body;
        static bool Constant(ManagedValue value) => value is ConstantValue
            || value is ComposedValue composed && composed.Leaves.All(p => Constant(p.Value));
        FieldValue? OwnField(ManagedValue value) => value is FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null } field
            && field.Field.Field.Owner == method.Owner ? field : null;
        FieldValue? Root(ManagedValue value) => OwnField(value)
            ?? (FieldPath(value, write: true) is { } path && !ManagedValues.Walk(value).OfType<FieldValue>().Any(f => f.Accessor is not null)
                ? OwnField(path.Root) : null);
        var entry = body.Blocks[0];
        var prefix = entry.Statements.TakeWhile(s => s is ManagedStore store && Root(store.Target) is not null && Constant(store.Value))
            .Cast<ManagedStore>().ToArray();
        if (prefix.Length < 2) return body;
        var replacements = new Dictionary<ManagedStore, ManagedStore>();
        var removed = new HashSet<ManagedStore>();
        foreach (var group in prefix.GroupBy(s => Root(s.Target)!))
        {
            var destination = group.Key;
            if (destination.Type is not DefinitionRef type || LeafPaths(type) is not { Count: > 1 } paths) continue;
            var writes = group.ToArray();
            if (writes.Any(s => FieldPath(s.Target, write: true) is not { } path || path.Root != destination)
                || !SamePaths(paths, writes.Select(s => FieldPath(s.Target, write: true)!.Value.Path))) continue;
            var leaves = writes.Select(s => (FieldPath(s.Target, write: true)!.Value.Path, s.Value)).ToArray();
            replacements[writes[0]] = new(writes[0].Address, destination, new ComposedValue(type, leaves));
            removed.UnionWith(writes.Skip(1));
        }
        if (replacements.Count == 0) return body;
        return body with { Blocks = [entry with { Statements = entry.Statements.Where(s => s is not ManagedStore store || !removed.Contains(store))
            .Select(s => s is ManagedStore store && replacements.TryGetValue(store, out var replacement) ? replacement : s).ToArray() }, .. body.Blocks.Skip(1)] };
    }
}
