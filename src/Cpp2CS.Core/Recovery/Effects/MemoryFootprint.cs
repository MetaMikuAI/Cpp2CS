using System.Reflection;

namespace Cpp2CS.Recovery.Effects;

/// <summary>可别名存储的字段路径；引用可能指向同一根，未知位置不能证明互不重叠。</summary>
public sealed record MemoryFootprint(MemoryKind Kind, TypeRef? Statics, TypeRef? Root, IReadOnlyList<FieldRef> Path)
{
    public static MemoryFootprint? Of(ManagedValue location, Func<ManagedValue, ManagedValue>? unwrap = null)
    {
        var path = new List<FieldRef>();
        var value = Unwrapped(location);
        for (var steps = 0; steps < 32; steps++)
        {
            switch (value)
            {
                case FieldValue field:
                    path.Insert(0, field.Field);
                    var receiver = Unwrapped(field.Receiver);
                    // 值类型字段内的字段属于同一存储；对象引用开始新的根。
                    if (receiver is FieldValue or StaticFieldValue or ArrayElementValue && !ManagedTypes.IsReferenceType(receiver.Type))
                    {
                        value = receiver;
                        continue;
                    }
                    return receiver.Type is ByRefRef or PointerRef
                        ? new(MemoryKind.Reference, null, receiver.Type is ByRefRef byRef ? byRef.Element : ((PointerRef)receiver.Type).Element, path)
                        : new(MemoryKind.Instance, null, null, path);
                case StaticFieldValue field:
                    path.Insert(0, field.Field);
                    return new(MemoryKind.Static, field.Field.DeclaringType, null, path);
                case ArrayElementValue element:
                    return new(MemoryKind.Element, null, element.Type, path);
                default:
                    return null;
            }
        }
        return null;

        ManagedValue Unwrapped(ManagedValue value)
        {
            value = unwrap?.Invoke(value) ?? value;
            while (value is AddressValue or IndirectValue)
                value = unwrap?.Invoke(value is AddressValue a ? a.Target : ((IndirectValue)value).Address)
                    ?? (value is AddressValue address ? address.Target : ((IndirectValue)value).Address);
            return value;
        }
    }

    /// <summary>
    /// 两个位置可能共享存储。根的种类相同（静态字段还须同一类型）时比较字段路径；经引用的位置可以落在另一位置中
    /// 任何被引用类型的值内，从那里起比较路径。不能识别的位置保守视为可能重叠。
    /// </summary>
    public static bool MayAlias(MemoryFootprint? x, MemoryFootprint? y)
    {
        if (x is null || y is null) return true;
        if (x.Kind == MemoryKind.Reference && y.Kind == MemoryKind.Reference)
            return Equals(x.Root, y.Root) ? Overlap(x.Path, y.Path) : Inside(x, y) || Inside(y, x);
        if (x.Kind == MemoryKind.Reference) return Inside(x, y);
        if (y.Kind == MemoryKind.Reference) return Inside(y, x);
        if (x.Kind != y.Kind || x.Kind == MemoryKind.Static && !Equals(x.Statics, y.Statics)) return false;
        return Overlap(x.Path, y.Path);

        // 经引用的位置 reference 落在 other 中某个被引用类型的值内，从那里起路径重叠。
        static bool Inside(MemoryFootprint reference, MemoryFootprint other)
        {
            for (var k = 0; k <= other.Path.Count; k++)
            {
                var container = k == 0 ? other.Root : FieldType(other.Path[k - 1]);
                if (container is not null && container.Equals(reference.Root) && Overlap(other.Path.Skip(k).ToArray(), reference.Path)) return true;
            }
            return false;
        }
        static TypeRef FieldType(FieldRef field) => field.DeclaringType is DefinitionRef owner ? field.Field.Type.Substitute(owner.Arguments, []) : field.Field.Type;
    }

    /// <summary>同一根下的两条字段路径重叠：一条是另一条的前缀，或在显式布局的同一类型中分叉。</summary>
    public static bool Overlap(IReadOnlyList<FieldRef> x, IReadOnlyList<FieldRef> y)
    {
        for (var i = 0; i < Math.Min(x.Count, y.Count); i++)
        {
            if (x[i].Equals(y[i])) continue;
            var owner = x[i].Field.Owner;
            return owner == y[i].Field.Owner && (owner.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout;
        }
        return true;
    }

}
