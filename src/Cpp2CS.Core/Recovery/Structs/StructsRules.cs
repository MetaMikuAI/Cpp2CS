using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class StructsRules
{
    internal static IEnumerable<(FieldRef[] Path, TypeRef Type, int Offset)> StructPaths(this RecoveryScope ctx, TypeRef type, int offset = 0, FieldRef[]? path = null)
    {
        path ??= [];
        if (type is ByRefRef b)
            type = b.Element;
        if (type is not DefinitionRef d || ctx.facts.Layouts.Of(d) is not { } layout)
            yield break;
        foreach (var slot in layout.Fields)
        {
            var at = offset + slot.Offset - (d.Definition.IsValueType ? RuntimeLayout.ObjectHeaderSize : 0);
            var fields = path.Append(new FieldRef(slot.Field, d)).ToArray();
            yield return (fields, slot.Type, at);
            if (ctx.types.Kind(slot.Type) == TypeKind.Struct)
                foreach (var nested in ctx.StructPaths(slot.Type, at, fields))
                    yield return nested;
        }

        // 基类中的结构体仍以整个对象为根，字段偏移不再叠加一层对象头。
        if (!d.Definition.IsValueType && d.Definition.BaseType?.Substitute(d.Arguments, []) is { } parent)
            foreach (var inherited in ctx.StructPaths(parent, offset, path))
                yield return inherited;
    }

    internal static ManagedValue PathValue(this RecoveryScope ctx, ManagedValue root, IReadOnlyList<FieldRef> path)
    {
        var value = root;
        foreach (var field in path)
        {
            if (ctx.types.Kind(value.Type) == TypeKind.Struct)
                value = new AddressValue(value);
            var type = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
            value = new FieldValue(value, field, type, ctx.types.Kind(type) == TypeKind.Struct ? 0 : Math.Max(8, ctx.types.Bits(type)));
        }

        return value;
    }

    internal static IEnumerable<(FieldRef[] Path, TypeRef Type, int Offset)> ScalarStructPaths(this RecoveryScope ctx, TypeRef type)
    {
        // 字段路径只依赖元数据和具体类型；同一方法的推断轮次共享展开结果。
        if (!ctx.State.Structs.scalarPaths.TryGetValue(type, out var paths))
            ctx.State.Structs.scalarPaths[type] = paths = BuildScalarStructPaths(ctx, type).ToArray();
        return paths;
    }

    private static IEnumerable<(FieldRef[] Path, TypeRef Type, int Offset)> BuildScalarStructPaths(RecoveryScope ctx, TypeRef type)
    {
        var leaves = ctx.StructPaths(type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null)).ToArray();
        foreach (var leaf in leaves)
        {
            var field = leaf.Path[^1].Field;
            var alias = (field.Attributes & System.Reflection.FieldAttributes.FieldAccessMask) == System.Reflection.FieldAttributes.Private && (field.Owner.Attributes & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout && ctx.types.Kind(leaf.Type) == TypeKind.Int;
            if (alias)
            {
                var cursor = leaf.Offset;
                // 同级窄整数字段完整覆盖私有宽别名时，访问权限不影响其位布局证据。
                var parts = leaves.Where(p => p.Path.Length == leaf.Path.Length && p.Path.SkipLast(1).SequenceEqual(leaf.Path.SkipLast(1))
                    && ((p.Path[^1].Field.Attributes & System.Reflection.FieldAttributes.FieldAccessMask) == System.Reflection.FieldAttributes.Public || ctx.types.Size(p.Type) < ctx.types.Size(leaf.Type))
                    && ctx.types.Kind(p.Type) == TypeKind.Int && p.Offset >= leaf.Offset && p.Offset + ctx.types.Size(p.Type) <= leaf.Offset + ctx.types.Size(leaf.Type)).OrderBy(p => p.Offset).ToArray();
                foreach (var part in parts)
                {
                    if (part.Offset != cursor)
                        break;
                    cursor += ctx.types.Size(part.Type);
                }

                if (cursor == leaf.Offset + ctx.types.Size(leaf.Type))
                    continue;
            }

            yield return leaf;
        }
    }

    internal static IReadOnlyList<TypeRef>? StructReceiverArguments(this RecoveryScope ctx, Expr? receiver, TypeDef owner)
    {
        if (receiver is null)
            return null;
        var (root, offset, rest) = ctx.Split(receiver);
        if (root is null || rest.Count != 0 || ctx.TypeOfAddressBase(root) is not { } rootType)
            return null;
        var paths = ctx.StructPaths(rootType).Where(p => p.Offset == offset && p.Type is DefinitionRef d && d.Definition == owner).ToArray();
        return paths.Length == 1 && paths[0].Type is DefinitionRef found ? found.Arguments : null;
    }
}
