using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Locations;

/// <summary>地址没有读取宽度；以一个字节定位，再保留声明位置的起点及其全部类型视图。</summary>
public sealed class ManagedAddressQuery(ManagedLocationQuery locations) : Query<Term, ImmutableArray<LocationView>>
{
    public override Outcome<ImmutableArray<LocationView>> Compute(QueryContext c, Term key)
    {
        if (key.Width != c.Snapshot.AddressWidth)
            return Outcome<ImmutableArray<LocationView>>.Failure(new("address.width", "项的位宽不是地址位宽。"));
        var resolved = c.Get(locations.State.Resolve, key); if (!resolved.IsSuccess) return resolved.Propagate<ImmutableArray<LocationView>>();
        var native = c.Get(locations.State.Locations, new(resolved.Value, 8)); if (!native.IsSuccess) return native.Propagate<ImmutableArray<LocationView>>();
        if (native.Value.Region is Region.Image or Region.Thread)
            return Outcome<ImmutableArray<LocationView>>.Failure(new("address.location", "映像或线程区域没有受支持的托管地址。"));
        var located = locations.Locate(c, new(resolved.Value, 8), true); if (!located.IsSuccess) return located.Propagate<ImmutableArray<LocationView>>();
        if (native.Value.Region == Region.Frame && located.Value.Kind == ManagedLocationKind.NotManaged)
            return Outcome<ImmutableArray<LocationView>>.Failure(new("address.frame", "帧对象的地址与生存期尚未下降。"));
        var exact = located.Value.Views.Where(v => v.Offset == 0 && v.Kind is
            ManagedLocationKind.FrameLocal or ManagedLocationKind.InstanceField or ManagedLocationKind.StaticField or ManagedLocationKind.ArrayElement).ToImmutableArray();
        if (exact.IsEmpty)
            return Outcome<ImmutableArray<LocationView>>.Failure(new("address.location", "地址未落在字段或数组元素的声明起点。", located.Value.Why));
        if (exact.Any(v => v.Kind == ManagedLocationKind.ArrayElement && ManagedTypes.IsReferenceType(v.ElementType ?? v.Type)))
            return Outcome<ImmutableArray<LocationView>>.Failure(new("address.reference-element", "引用类型数组元素的取址与类型检查尚未下降。"));
        return Outcome<ImmutableArray<LocationView>>.Success(exact);
    }
}
