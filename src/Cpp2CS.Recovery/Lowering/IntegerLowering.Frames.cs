using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private FrameObjects? frameObjects;
    private readonly FrameAddressUseQuery frameAddressUses;
    private readonly Dictionary<FrameObject, LocalValue> frameLocals = [];
    private void PrepareFrameObjects()
    {
        var query = new FrameObjectQuery(state, types, [.. callDefinitions.Select(p =>
            new FrameCall(p.Key, p.Value.Method, p.Value.Binding, p.Value.Receiver))], binder, signature, method, frameAddressUses);
        var answer = context.Get(query, 0);
        if (!answer.IsSuccess)
        { Fail<object>(LoweringFailureKind.UnsupportedType, answer.Why!.Message, answer.Why.Cause, answer.Why.Code); return; }
        frameObjects = answer.Value;
        if (!frameObjects.Objects.IsEmpty && spec is not null && calls is not null)
        {
            // 新查询实例消费固定的帧认定结果；不改变旧上下文里已缓存的位置或类型。
            var naming = new Cpp2CS.Recovery.Naming.ValueNamingQuery(state, calls, names, spec, binder, signature);
            valueNames = naming;
            locations = new(state, naming, types.Layouts, spec, frameObjects);
            dispatch = new(state, calls, naming, locations, binder, spec);
            context = locations.CreateContext(function);
        }
    }
    private bool FrameContains(Location location) => frameObjects?.Accesses.Values.Any(a => a.Location == location) == true;
    private LocalValue FrameLocal(FrameObject item)
    {
        if (!frameLocals.TryGetValue(item, out var local))
            frameLocals.Add(item, local = new(new(nextLocal++), item.Type, types.ValueWidth(item.Type)));
        return local;
    }
    private ManagedStatement? FrameCallResult(Call call)
    {
        if (frameObjects is null || !frameObjects.Results.TryGetValue(call.Identity, out var item)) return null;
        // 调用结果局部是不可变的快照；帧对象本身仍可被后续调用改写。
        var value = CallResult(callDefinitions[call.Identity]);
        return value is null ? null : new ManagedAssignment(position, FrameLocal(item), value);
    }
    private IReadOnlyList<ManagedStatement> LowerStores(MemoryWrite write, Point point)
    {
        if (frameObjects is null || !frameObjects.Accesses.TryGetValue(write.Identity, out var access))
        {
            var statement = LowerStore(write, point);
            return statement is null ? [] : [statement];
        }
        if (frameObjects.CopyRemainders.Contains(write.Identity)) return [];
        if (RejectAddressUse([write.Value], "写入内存")) return [];
        if (frameObjects.Copies.TryGetValue(write.Identity, out var copy))
        {
            var whole = StructValue(copy.Source, copy.Object.Type, copy.Point);
            return whole is null ? [] : [new ManagedAssignment(position, FrameLocal(copy.Object), whole)];
        }
        var statements = new List<ManagedStatement>();
        int start = (int)((access.Location.Offset!.Value - access.Object.Storage.Offset!.Value) * 8);
        foreach (var part in access.Parts)
        {
            var view = new LocationView(ManagedLocationKind.FrameLocal, access.Object.Address, part.Type, [.. part.Path],
                0, part.Width, null, null);
            if (!WritableStructPath(part.Path)) return [];
            var target = AccessView(view, true); if (target is null) return [];
            var value = Part(write.Value, part.Bit - start, part.Width, IsFloat(part.Type)); if (value is null) return [];
            value = ReferenceType(part.Type) ? Coerce(value, part.Type) : IsFloat(part.Type) ? FloatBits(value, part.Width)
                : new ConversionValue(ManagedTypes.IsSigned(part.Type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                    IntegerBits(value), part.Type, part.Width);
            statements.Add(target is LocalValue local ? new ManagedAssignment(position, local, value) : new ManagedStore(position, target, value));
        }
        return statements;
    }
}
