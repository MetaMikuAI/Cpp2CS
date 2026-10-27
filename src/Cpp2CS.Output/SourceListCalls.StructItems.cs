using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

internal static partial class SourceListCalls
{
    // 结构体元素可按字段写入；仅在全部叶子各写一次、没有其他操作时合成整值。
    private static (ArrayElementValue Element, ManagedValue Value)? ReadElement(ManagedStatement? first,
        Func<ManagedStatement?> next, ManagedTypes types, List<ManagedStatement> writes,
        Func<MethodRef, SourceValueConstructor?>? constructor)
    {
        if (first is ManagedStore { Target: ArrayElementValue direct } whole)
        {
            writes.Add(whole);
            return (direct, ExpandItem(whole.Value, constructor));
        }
        static (ArrayElementValue Element, FieldRef[] Path)? Location(ManagedValue value)
        {
            if (value is AddressValue addressValue) value = addressValue.Target;
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
        (ManagedValue Target, ManagedValue Value)? Write(ManagedStatement? statement) => statement switch
        {
            ManagedStore store => (store.Target, store.Value),
            ManagedCall { Tail: false, Result: null, Invocation: { Virtual: false, Receiver: { } receiver } call }
                when constructor?.Invoke(call.Method)?.Expand(call.Arguments) is { } value => (receiver, value),
            _ => null,
        };
        if (Write(first) is not { } initial || Location(initial.Target) is not { } location
            || Leaves(location.Element.Type) is not { Count: > 0 } expected) return null;
        var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        ManagedStatement? current = first;
        while (leaves.Count < expected.Count)
        {
            if (Write(current) is not { } write || Location(write.Target) is not { } target || !target.Element.Equals(location.Element)) return null;
            var value = ExpandItem(write.Value, constructor);
            var components = value is ComposedValue composed
                ? composed.Leaves.Select(p => ((IReadOnlyList<FieldRef>)target.Path.Concat(p.Path).ToArray(), p.Value)).ToArray()
                : [((IReadOnlyList<FieldRef>)target.Path, value)];
            if (components.Length == 0) return null;
            foreach (var (path, leaf) in components)
            {
                if (!expected.Any(p => p.SequenceEqual(path)) || leaves.Any(p => p.Path.SequenceEqual(path))) return null;
                leaves.Add((path, leaf));
            }
            writes.Add(current!);
            if (leaves.Count < expected.Count) current = next();
        }
        return (location.Element, new ComposedValue(location.Element.Type, leaves));
    }

    private static ManagedValue ExpandItem(ManagedValue value, Func<MethodRef, SourceValueConstructor?>? constructor, int depth = 0)
    {
        if (depth > 16) return value;
        if (value is NewObjectValue created && constructor?.Invoke(created.Constructor)?.Expand(created.Arguments) is { } expanded)
            value = expanded;
        if (value is not ComposedValue composed) return value;
        var leaves = new List<(IReadOnlyList<FieldRef>, ManagedValue)>();
        foreach (var (path, original) in composed.Leaves)
        {
            var leaf = ExpandItem(original, constructor, depth + 1);
            if (leaf is ComposedValue { Leaves.Count: > 0 } nested)
                leaves.AddRange(nested.Leaves.Select(p => ((IReadOnlyList<FieldRef>)path.Concat(p.Path).ToArray(), p.Value)));
            else leaves.Add((path, leaf));
        }
        return composed with { Leaves = leaves };
    }

    private static bool SameItem(ManagedValue left, ManagedValue right) => left.Equals(right)
        || left is ComposedValue a && right is ComposedValue b && a.Type.Equals(b.Type) && a.Leaves.Count == b.Leaves.Count
            && a.Leaves.All(p => b.Leaves.Count(q => q.Path.SequenceEqual(p.Path) && SameItem(p.Value, q.Value)) == 1)
            && b.Leaves.All(q => a.Leaves.Count(p => p.Path.SequenceEqual(q.Path) && SameItem(p.Value, q.Value)) == 1);
}
