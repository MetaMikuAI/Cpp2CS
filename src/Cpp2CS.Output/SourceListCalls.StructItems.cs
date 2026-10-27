using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

internal static partial class SourceListCalls
{
    // 结构体元素可按字段写入；仅在全部叶子各写一次、没有其他操作时合成整值。
    private static (ArrayElementValue Element, ManagedValue Value)? ReadElement(ManagedStatement? first,
        Func<ManagedStatement?> next, ManagedTypes types, List<ManagedStore> writes)
    {
        if (first is ManagedStore { Target: ArrayElementValue direct } whole)
        {
            writes.Add(whole);
            return (direct, whole.Value);
        }
        static (ArrayElementValue Element, FieldRef[] Path)? Location(ManagedValue value)
        {
            var path = new List<FieldRef>();
            while (value is FieldValue { Accessor: null } field)
            {
                path.Insert(0, field.Field);
                value = field.Receiver is AddressValue address ? address.Target : field.Receiver;
                if (value.Type is not DefinitionRef { Definition.IsValueType: true }) return null;
            }
            return value is ArrayElementValue element && path.Count != 0 ? (element, path.ToArray()) : null;
        }
        List<FieldRef[]>? Leaves(TypeRef type, int depth = 0)
        {
            if (depth > 16 || type is not DefinitionRef definition || types.Kind(type) != TypeKind.Struct
                || (definition.Definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout) return null;
            var paths = new List<FieldRef[]>();
            foreach (var field in definition.Definition.Fields.Where(f => !f.IsStatic))
            {
                var reference = new FieldRef(field, definition);
                var fieldType = field.Type.Substitute(definition.Arguments, []);
                if (types.Kind(fieldType) == TypeKind.Struct)
                {
                    if (Leaves(fieldType, depth + 1) is not { Count: > 0 } nested) return null;
                    paths.AddRange(nested.Select(p => new[] { reference }.Concat(p).ToArray()));
                }
                else paths.Add([reference]);
            }
            return paths;
        }
        if (first is not ManagedStore initial || Location(initial.Target) is not { } location
            || Leaves(location.Element.Type) is not { Count: > 0 } expected) return null;
        var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        ManagedStatement? current = first;
        while (leaves.Count < expected.Count)
        {
            if (current is not ManagedStore store || Location(store.Target) is not { } target || !target.Element.Equals(location.Element)
                || !expected.Any(p => p.SequenceEqual(target.Path)) || leaves.Any(p => p.Path.SequenceEqual(target.Path))) return null;
            leaves.Add((target.Path, store.Value));
            writes.Add(store);
            if (leaves.Count < expected.Count) current = next();
        }
        return (location.Element, new ComposedValue(location.Element.Type, leaves));
    }

    private static bool SameItem(ManagedValue left, ManagedValue right) => left.Equals(right)
        || left is ComposedValue a && right is ComposedValue b && a.Type.Equals(b.Type) && a.Leaves.Count == b.Leaves.Count
            && a.Leaves.All(p => b.Leaves.Count(q => q.Path.SequenceEqual(p.Path) && SameItem(p.Value, q.Value)) == 1)
            && b.Leaves.All(q => a.Leaves.Count(p => p.Path.SequenceEqual(q.Path) && SameItem(p.Value, q.Value)) == 1);
}
