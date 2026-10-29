using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {

        /// <summary>L1 的值类型每层偏移含 0x10 对象头；ByRef 指向未装箱数据，逐层扣除。</summary>
        private IEnumerable<(FieldRef[] Path, TypeRef Type, int Offset)> StructPaths(TypeRef type, int offset = 0, FieldRef[]? path = null)
        {
            path ??= [];
            if (type is ByRefRef b) type = b.Element;
            if (type is not DefinitionRef d || facts.Layouts.Of(d) is not { } layout) yield break;
            foreach (var slot in layout.Fields)
            {
                var at = offset + slot.Offset - (d.Definition.IsValueType ? RuntimeLayout.ObjectHeaderSize : 0);
                var fields = path.Append(new FieldRef(slot.Field, d)).ToArray();
                yield return (fields, slot.Type, at);
                if (types.Kind(slot.Type) == TypeKind.Struct)
                    foreach (var nested in StructPaths(slot.Type, at, fields)) yield return nested;
            }
            // 基类中的结构体仍以整个对象为根，字段偏移不再叠加一层对象头。
            if (!d.Definition.IsValueType && d.Definition.BaseType?.Substitute(d.Arguments, []) is { } parent)
                foreach (var inherited in StructPaths(parent, offset, path)) yield return inherited;
        }

        private ManagedValue PathValue(ManagedValue root, IReadOnlyList<FieldRef> path)
        {
            var value = root;
            foreach (var field in path)
            {
                if (types.Kind(value.Type) == TypeKind.Struct) value = new AddressValue(value);
                var type = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
                value = new FieldValue(value, field, type, types.Kind(type) == TypeKind.Struct ? 0 : Math.Max(8, types.Bits(type)));
            }
            return value;
        }

        /// <summary>私有整数别名被同一显式布局中的公开整数分量完整覆盖时，使用互不重叠的公开分量。</summary>
        private IEnumerable<(FieldRef[] Path, TypeRef Type, int Offset)> ScalarStructPaths(TypeRef type)
        {
            var leaves = StructPaths(type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)).ToArray();
            foreach (var leaf in leaves)
            {
                var field = leaf.Path[^1].Field;
                var alias = (field.Attributes & System.Reflection.FieldAttributes.FieldAccessMask) == System.Reflection.FieldAttributes.Private
                    && (field.Owner.Attributes & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout
                    && types.Kind(leaf.Type) == TypeKind.Int;
                if (alias)
                {
                    var cursor = leaf.Offset;
                    var parts = leaves.Where(p => p.Path.Length == leaf.Path.Length && p.Path.SkipLast(1).SequenceEqual(leaf.Path.SkipLast(1))
                        && (p.Path[^1].Field.Attributes & System.Reflection.FieldAttributes.FieldAccessMask) == System.Reflection.FieldAttributes.Public
                        && types.Kind(p.Type) == TypeKind.Int && p.Offset >= leaf.Offset && p.Offset + types.Size(p.Type) <= leaf.Offset + types.Size(leaf.Type))
                        .OrderBy(p => p.Offset).ToArray();
                    foreach (var part in parts)
                    {
                        if (part.Offset != cursor) break;
                        cursor += types.Size(part.Type);
                    }
                    if (cursor == leaf.Offset + types.Size(leaf.Type)) continue;
                }
                yield return leaf;
            }
        }

        private IReadOnlyList<TypeRef>? StructReceiverArguments(Expr? receiver, TypeDef owner)
        {
            if (receiver is null) return null;
            var (root, offset, rest) = Split(receiver);
            if (root is null || rest.Count != 0 || TypeOfAddressBase(root) is not { } rootType) return null;
            var paths = StructPaths(rootType).Where(p => p.Offset == offset && p.Type is DefinitionRef d && d.Definition == owner).ToArray();
            return paths.Length == 1 && paths[0].Type is DefinitionRef found ? found.Arguments : null;
        }
    }
}
