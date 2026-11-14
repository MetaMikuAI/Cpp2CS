using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private ManagedValue? MissingMemoryValue(MemoryAtom memory)
    {
        var location = memory.Location;
        var address = location.UnknownOffsetAddress ?? location.Root;
        string kind, detail;
        if (SnapshotRewrite.Dependencies([address]).Any(t => t.Identity is ResultAtom { Definition: ReadIdentity }))
            (kind, detail) = ("UnresolvedReadAddress", "位来源的读取地址仍含未解析的读取结果");
        else if (location.Region != Region.Frame && merges.Keys.Any(k =>
            k.Term.Identity is MemoryMerge merge && merge.Location == location))
            (kind, detail) = ("NonFrameMerge", "合流处的非帧读取没有原读取局部，内存版本被展开为各路径的值");
        else if (location.Region != Region.Frame)
            (kind, detail) = ("ReadFragment", "非帧内存的读取片段没有可下降的原读取定义");
        else if (memory.Definition is CallIdentity)
        {
            var escaped = context.Get(state.Escapes, 0);
            (kind, detail) = escaped.IsSuccess && escaped.Value.MayReach(location)
                ? ("EscapedFrameCall", "取址帧范围的读取到达调用的可能改写，缺少可下降的原读取或帧对象值")
                : ("FrameCallArea", "帧读取到达调用的效果或传出实参区，缺少可下降的写入定义");
        }
        else if (memory.Definition is WriteIdentity)
            (kind, detail) = ("FrameAliasedWrite", "帧读取到达不能确定重叠范围的写入");
        else if (StackParameter(location))
            (kind, detail) = ("StackParameter", "读取调用方帧中的栈形参，入口绑定尚未提供托管值");
        else
            (kind, detail) = ("FrameEntry", "帧读取到达入口，缺少已绑定的形参或写入定义");
        return Fail<ManagedValue>(LoweringFailureKind.State,
            $"{detail}：区域 {location.Region}，偏移 {location.Offset?.ToString() ?? "未知"}，位宽 {location.Width}",
            code: "lowering.State." + kind);
    }

    private bool StackParameter(Location location)
    {
        if (function.IncomingArgumentArea is not { } area || signature.Managed is not { } managed) return false;
        var incoming = context.Get(state.Locations, new(area, location.Width));
        if (!incoming.IsSuccess || location.Root != incoming.Value.Root || location.Offset is not { } offset
            || incoming.Value.Offset is not { } start) return false;
        return managed.ParameterIndices.SelectMany(i => signature.Slots.Parameters[i].Pieces)
            .Any(p => p.Slot.Kind == SlotKind.ArgumentArea && offset >= start + p.Slot.Position + p.SlotOffset
                && offset * 8 + location.Width <= (start + p.Slot.Position + p.SlotOffset + p.Length) * 8);
    }

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
            var naming = new Cpp2CS.Recovery.Naming.ValueNamingQuery(state, calls, names, spec, binder, signature, rgctx, types.Layouts as Cpp2CS.Recovery.Binding.GenericWitness);
            valueNames = naming;
            locations = new(state, naming, types.Layouts, spec, frameObjects);
            dispatch = new(state, calls, naming, locations, binder, spec, types.Layouts as Cpp2CS.Recovery.Binding.GenericWitness);
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
            var resolved = context.Get(state.Resolve, write.Address);
            if (resolved.IsSuccess && context.Get(state.Locations, new(resolved.Value, write.Width)) is { IsSuccess: true } native
                && native.Value.Region != Region.Frame && RangeStores(write, point) is { } split) return split;
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
        var leaves = access.Parts.Select(part => new LocationPiece(new LocationView(ManagedLocationKind.FrameLocal,
            access.Object.Address, part.Type, [.. part.Path], 0, part.Width, null, null), part.Bit - start, 0, part.Width)).ToArray();
        var aggregates = write.Width > 64 ? ManagedRangeQuery.WholeStructures(types, leaves, write.Width) : [];
        foreach (var piece in WidePieces(write, point, leaves, aggregates))
        {
            var view = piece.View!;
            if (!WritableStructPath(view.Path)) return [];
            var target = AccessView(view, true); if (target is null) return [];
            var value = types.Kind(view.Type) == TypeKind.Struct ? WideStructValue(write, point, piece)
                : Part(write.Value, piece.AccessBit, piece.Width, IsFloat(view.Type)); if (value is null) return [];
            value = types.Kind(view.Type) == TypeKind.Struct ? value : ReferenceType(view.Type) ? Coerce(value, view.Type) : IsFloat(view.Type) ? FloatBits(value, piece.Width)
                : new ConversionValue(ManagedTypes.IsSigned(view.Type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                    IntegerBits(value), view.Type, piece.Width);
            statements.Add(target is LocalValue local ? new ManagedAssignment(position, local, value) : new ManagedStore(position, target, value));
        }
        return statements;
    }
}
