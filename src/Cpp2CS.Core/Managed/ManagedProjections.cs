namespace Cpp2CS.Managed;

/// <summary>已求值整体的字段关系。Discarded 的求值不能因取字段而被删除。</summary>
public sealed record ManagedProjection(ManagedValue Value, IReadOnlyList<ManagedValue> Discarded);

/// <summary>按布局投影托管值。读取的观察时刻由使用方提供，不创建或猜测内存版本。</summary>
public static class ManagedProjections
{
    public static ManagedProjection? Project(ManagedTypes types, ManagedValue value, ValueProjection projection,
        Func<FieldValue, ManagedValue> observe)
    {
        if (value.Type is not DefinitionRef structure || types.Project(structure, projection.Path) is not { } verified
            || verified.Bit != projection.Bit || verified.Width != projection.Width || !verified.Type.Equals(projection.Type)) return null;
        if (value is not ComposedValue composed)
        {
            foreach (var field in projection.Path)
            {
                var type = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
                value = observe(new FieldValue(value, field, type, types.ValueWidth(type)));
            }
            return new(value, []);
        }

        // initobj 后的字段写入须互不重叠；否则最后一次写入决定内容，不能只比较字段集合。
        var ranges = composed.Leaves.Select(l => types.Project(structure, l.Path)).ToArray();
        if (ranges.Any(p => p is null)) return null;
        var ordered = ranges.OrderBy(p => p!.Bit).ToArray();
        if (ordered.Zip(ordered.Skip(1)).Any(p => (long)p.First!.Bit + p.First.Width > p.Second!.Bit)) return null;

        var parent = composed.Leaves.FirstOrDefault(l => Prefix(l.Path, projection.Path));
        if (parent.Value is not null)
        {
            var discarded = composed.Leaves.Where(l => !l.Path.SequenceEqual(parent.Path)).Select(l => l.Value).ToArray();
            if (parent.Path.Count == projection.Path.Count)
                return parent.Value.Type.Equals(projection.Type) ? new(parent.Value, discarded) : null;
            if (parent.Value.Type is not DefinitionRef nested
                || types.Project(nested, projection.Path.Skip(parent.Path.Count).ToArray()) is not { } inner
                || Project(types, parent.Value, inner, observe) is not { } projected) return null;
            return projected with { Discarded = [.. discarded, .. projected.Discarded] };
        }

        var children = composed.Leaves.Where(l => Prefix(projection.Path, l.Path)).ToArray();
        ManagedValue result;
        if (children.Length > 0)
        {
            if (types.Kind(projection.Type) != TypeKind.Struct) return null;
            result = new ComposedValue(projection.Type, children.Select(l =>
                ((IReadOnlyList<FieldRef>)l.Path.Skip(projection.Path.Count).ToArray(), l.Value)).ToArray());
        }
        else result = types.Kind(projection.Type) == TypeKind.Struct ? new ComposedValue(projection.Type, [])
            : new ConstantValue(0, projection.Type, types.ValueWidth(projection.Type));
        return new(result, composed.Leaves.Where(l => !Prefix(projection.Path, l.Path)).Select(l => l.Value).ToArray());
    }

    private static bool Prefix(IReadOnlyList<FieldRef> prefix, IReadOnlyList<FieldRef> path) =>
        path.Count >= prefix.Count && path.Take(prefix.Count).SequenceEqual(prefix);
}
