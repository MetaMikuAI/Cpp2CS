using System.Reflection;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 模板比对中位置的别名与读写依赖，只在此处判定。位置的足迹是存储根与根内的值类型字段路径：
/// 实例字段的根是对象引用（或引用参数），静态字段的根是所在类型的静态存储，数组元素的根是元素本身。
/// 不同对象引用可能指向同一对象，因此实例字段不比较根；两条路径一条是另一条的前缀（整个结构体与其内部字段）时重叠；
/// 显式布局的同一类型中不同字段保守视为重叠。
/// </summary>
internal sealed partial class TemplateRecovery
{
    private enum StorageKind { Instance, Static, Element, Reference }

    /// <summary>位置的足迹。Root 是元素类型（数组元素）或被引用的类型（经引用或指针）；路径从根上的第一个字段起。</summary>
    private sealed record Footprint(StorageKind Kind, TypeRef? Statics, TypeRef? Root, IReadOnlyList<FieldRef> Path);

    private static Footprint? FootprintOf(ManagedValue location)
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
                        ? new(StorageKind.Reference, null, receiver.Type is ByRefRef byRef ? byRef.Element : ((PointerRef)receiver.Type).Element, path)
                        : new(StorageKind.Instance, null, null, path);
                case StaticFieldValue field:
                    path.Insert(0, field.Field);
                    return new(StorageKind.Static, field.Field.DeclaringType, null, path);
                case ArrayElementValue element:
                    return new(StorageKind.Element, null, element.Type, path);
                default:
                    return null;
            }
        }
        return null;

        static ManagedValue Unwrapped(ManagedValue value)
        {
            while (value is Observed or AddressValue or IndirectValue)
                value = value switch { Observed o => o.Read, AddressValue a => a.Target, IndirectValue i => i.Address, _ => value };
            return value;
        }
    }

    /// <summary>
    /// 两个位置可能共享存储。根的种类相同（静态字段还须同一类型）时比较字段路径；经引用的位置可以落在另一位置中
    /// 任何被引用类型的值内，从那里起比较路径。不能识别的位置只与自身相同。
    /// </summary>
    private static bool MayAlias(ManagedValue a, ManagedValue b)
    {
        if (a.Equals(b)) return true;
        if (FootprintOf(a) is not { } x || FootprintOf(b) is not { } y) return false;
        if (x.Kind == StorageKind.Reference && y.Kind == StorageKind.Reference)
            return Equals(x.Root, y.Root) ? Overlap(x.Path, y.Path) : Inside(x, y) || Inside(y, x);
        if (x.Kind == StorageKind.Reference) return Inside(x, y);
        if (y.Kind == StorageKind.Reference) return Inside(y, x);
        if (x.Kind != y.Kind || x.Kind == StorageKind.Static && !Equals(x.Statics, y.Statics)) return false;
        return Overlap(x.Path, y.Path);

        // 经引用的位置 reference 落在 other 中某个被引用类型的值内，从那里起路径重叠。
        static bool Inside(Footprint reference, Footprint other)
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
    private static bool Overlap(IReadOnlyList<FieldRef> x, IReadOnlyList<FieldRef> y)
    {
        for (var i = 0; i < Math.Min(x.Count, y.Count); i++)
        {
            if (x[i].Equals(y[i])) continue;
            var owner = x[i].Field.Owner;
            return owner == y[i].Field.Owner && (owner.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout;
        }
        return true;
    }

    /// <summary>项是否读取了可能与 location 共享存储的位置（包括作为接收者的读取）。</summary>
    private static bool ReadsLocation(ManagedValue value, ManagedValue location) => value switch
    {
        Observed observed => MayAlias(observed.Read, location) || ReadsLocation(observed.Read, location),
        Returned => false,
        _ => ManagedValues.Children(value).Any(child => ReadsLocation(child, location)),
    };
}
