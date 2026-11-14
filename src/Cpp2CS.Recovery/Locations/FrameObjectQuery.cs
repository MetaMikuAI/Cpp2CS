using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Locations;

public sealed record FrameAddressUse(Term Term, Location Location);

/// <summary>值中的帧地址用途；解析读取与合流来源，不把访问地址当成被读取的值。</summary>
public sealed class FrameAddressUseQuery(StateQueries state) : Query<Term, ImmutableArray<FrameAddressUse>>
{
    public override Outcome<ImmutableArray<FrameAddressUse>> Compute(QueryContext c, Term key)
    {
        var resolved = c.Get(state.Resolve, key); if (!resolved.IsSuccess) return resolved.Propagate<ImmutableArray<FrameAddressUse>>();
        var found = ImmutableArray.CreateBuilder<FrameAddressUse>();
        var pending = new Stack<Term>(); var seen = new HashSet<Term>(); pending.Push(resolved.Value);
        while (pending.TryPop(out var input))
        {
            var source = c.Get(state.Resolve, input); if (!source.IsSuccess) return source.Propagate<ImmutableArray<FrameAddressUse>>();
            var value = source.Value;
            if (!seen.Add(value)) continue;
            if (c.Step() is { } why) return Outcome<ImmutableArray<FrameAddressUse>>.Failure(why);
            if (value.Width == c.Snapshot.AddressWidth)
            {
                var native = c.Get(state.Locations, new(value, 8));
                if (native.IsSuccess && native.Value.Region == Region.Frame)
                { found.Add(new(value, native.Value)); continue; }
            }
            foreach (var operand in value.Operands) pending.Push(operand);
            if (value.Identity is ResultAtom { Definition: MergeIdentity id })
                foreach (var edge in c.Snapshot.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == id).Inputs) pending.Push(edge.Value);
        }
        return Outcome<ImmutableArray<FrameAddressUse>>.Success(found.ToImmutable());
    }
}

/// <summary>调用身份已由绑定与分派确定；帧认定只消费不可变的签名证据。</summary>
public sealed record FrameCall(CallIdentity Identity, MethodRef Method, BoundCall Binding, Term? Receiver = null);
public sealed record FramePointee(CallIdentity Identity, BoundSource Source, TypeRef Type);
public sealed record FrameClear(CallIdentity Identity, BoundSource Address, int Length);
public sealed record FrameObject(Location Storage, TypeRef Type, Term Address)
{
    public ImmutableArray<ValueProjection> Fields { get; init; } = [];
}
public sealed record FrameAccess(FrameObject Object, Location Location, ImmutableArray<ValueProjection> Parts);
public sealed record FrameCopy(FrameObject Object, BoundSource Source, Point Point);
public sealed record FrameObjects(ImmutableArray<FrameObject> Objects, ImmutableDictionary<StableIdentity, FrameAccess> Accesses)
{
    public ImmutableDictionary<CallIdentity, FrameObject> Results { get; init; } = ImmutableDictionary<CallIdentity, FrameObject>.Empty;
    public ImmutableDictionary<WriteIdentity, FrameCopy> Copies { get; init; } = ImmutableDictionary<WriteIdentity, FrameCopy>.Empty;
    public ImmutableHashSet<WriteIdentity> CopyRemainders { get; init; } = [];
    public ImmutableHashSet<WriteIdentity> AddressSpills { get; init; } = [];
    public ImmutableDictionary<CallIdentity, FrameObject> Clears { get; init; } = ImmutableDictionary<CallIdentity, FrameObject>.Empty;
    public LocationResult Locate(Location location)
    {
        if (location.Offset is not { } offset) return new(ManagedLocationKind.NotManaged, []);
        var item = Objects.SingleOrDefault(o => o.Storage.Root == location.Root && offset >= o.Storage.Offset
            && offset * 8 + location.Width <= o.Storage.Offset * 8 + o.Storage.Width);
        if (item is null) return new(ManagedLocationKind.NotManaged, []);
        var relative = offset - item.Storage.Offset!.Value;
        var views = ImmutableArray.CreateBuilder<LocationView>();
        views.Add(new(ManagedLocationKind.FrameLocal, item.Address, item.Type, [], relative, location.Width, null, null));
        foreach (var field in item.Fields.Where(f => f.Contains((int)relative * 8, location.Width)))
            views.Add(new(ManagedLocationKind.FrameLocal, item.Address, field.Type, [.. field.Path], relative - field.Bit / 8,
                location.Width, null, null));
        return new(ManagedLocationKind.FrameLocal, views.ToImmutable());
    }
}

/// <summary>取址用途、类型和直接访问的边界共同认定函数内可寻址的托管帧对象。</summary>
public sealed class FrameObjectQuery(StateQueries state, ManagedTypes types, ImmutableArray<FrameCall> calls,
    MethodBinder binder, SignatureBinding signature, MethodRef method, FrameAddressUseQuery addressUses,
    ImmutableArray<FramePointee> pointees = default, ImmutableArray<FrameClear> clears = default) : Query<int, FrameObjects>
{
    private readonly BoundSourceQuery sources = new(state);
    public override Outcome<FrameObjects> Compute(QueryContext c, int key)
    {
        var objects = new Dictionary<BigInteger, FrameObject>();
        var uses = new List<(Term Term, TypeRef? Element)>();
        var buffers = new List<(CallIdentity Call, Point Point, Term Pointer, TypeRef Type, int Length, bool Write)>();
        var indirectInputs = new HashSet<CallIdentity>();
        var spills = new Dictionary<WriteIdentity, Location>();
        var clearBuffers = new List<(FrameClear Clear, Term Pointer)>();
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<FrameObjects>();
        foreach (var block in c.Snapshot.Blocks)
        {
            for (int i = 0; i < block.Statements.Length; i++)
            {
                var point = new Point(block.Identity, i);
                switch (block.Statements[i])
                {
                    case MemoryWrite write:
                        if (write.Width == c.Snapshot.AddressWidth && write.Value.Width == c.Snapshot.AddressWidth)
                        {
                            var value = c.Get(state.Resolve, write.Value);
                            if (value.IsSuccess && c.Get(state.Locations, new(value.Value, 8)) is { IsSuccess: true, Value: { Region: Region.Frame, Offset: not null } })
                            {
                                var destination = c.Get(state.Resolve, write.Address);
                                if (destination.IsSuccess
                                    && c.Get(state.Locations, new(destination.Value, write.Width)) is { IsSuccess: true, Value: { Region: Region.Frame, Offset: not null } storage })
                                { spills.Add(write.Identity, storage); break; }
                            }
                        }
                        uses.Add((write.Value, null)); break;
                    case Call call:
                        if (!clears.IsDefault && clears.SingleOrDefault(p => p.Identity == call.Identity) is { } clear)
                        {
                            var pointer = c.Get(sources, new(clear.Address, point));
                            if (!pointer.IsSuccess) return pointer.Propagate<FrameObjects>();
                            clearBuffers.Add((clear, pointer.Value));
                        }
                        if (!pointees.IsDefault && pointees.SingleOrDefault(p => p.Identity == call.Identity) is { } pointee)
                        {
                            var pointer = c.Get(sources, new(pointee.Source, point));
                            if (!pointer.IsSuccess) return pointer.Propagate<FrameObjects>();
                            uses.Add((pointer.Value, pointee.Type));
                            buffers.Add((call.Identity, point, pointer.Value, pointee.Type, types.Size(pointee.Type), false));
                        }
                        var evidence = calls.SingleOrDefault(v => v.Identity == call.Identity);
                        if (evidence is null) continue;
                        var binding = evidence.Binding; var target = evidence.Method;
                        void Buffer(IndirectSource source, TypeRef type, bool write)
                        {
                            var pointer = c.Get(sources, new(source.Address, point));
                            if (pointer.IsSuccess)
                            {
                                buffers.Add((call.Identity, point, pointer.Value, type, source.Length, write));
                                if (!write) { uses.Add((pointer.Value, type)); indirectInputs.Add(call.Identity); }
                            }
                        }
                        void Input(BoundSource? source, TypeRef? type)
                        {
                            if (source is IndirectSource indirect && type is not null && types.Kind(type) == TypeKind.Struct)
                            { Buffer(indirect, type, false); return; }
                            var value = c.Get(sources, new(source, point));
                            if (value.IsSuccess) uses.Add((value.Value, (type as ByRefRef)?.Element));
                        }
                        for (int p = 0; p < binding.Parameters.Length; p++)
                            Input(binding.Parameters[p].Source, target.Concrete(target.Method.Parameters[p].Type));
                        if (evidence.Receiver is { } receiver)
                            uses.Add((receiver, target.Method.Owner.IsValueType ? target.DeclaringType : null));
                        else if (binding.This is { } self)
                            Input(self.Source, target.Method.Owner.IsValueType ? new ByRefRef(target.DeclaringType) : target.DeclaringType);
                        if (binding.MethodInformation is { } info) Input(info.Source, null);
                        if (binding.Result.Source is IndirectSource result && types.Kind(target.Concrete(target.Method.ReturnType)) == TypeKind.Struct)
                            Buffer(result, target.Concrete(target.Method.ReturnType), true);
                        break;
                }
            }
            if (block.End is Return returned && !ManagedTypes.IsVoid(method.Concrete(method.Method.ReturnType)))
            {
                var result = binder.Return(returned, signature, c.Snapshot.Terms,
                    c.Snapshot.Inputs.Select(v => new SlotValue(v.Slot, v.Value)).ToImmutableArray(), c.Snapshot.IncomingArgumentArea);
                var value = c.Get(sources, new(result.Value?.Source, new(block.Identity, block.Statements.Length)));
                if (value.IsSuccess) uses.Add((value.Value, null));
            }
            else if (block.End is Branch branch) uses.Add((branch.Condition, null));
            else if (block.End is JumpTable table) uses.Add((table.Selector, null));
        }
        // 先收齐类型见证；不把一次合法用途误作另一次用途的许可。
        foreach (var (term, element) in uses.Where(u => u.Element is not null))
        {
            var resolved = c.Get(state.Resolve, term); if (!resolved.IsSuccess) return resolved.Propagate<FrameObjects>();
            var native = c.Get(state.Locations, new(resolved.Value, 8));
            if (!native.IsSuccess || native.Value.Region != Region.Frame) continue;
            if (native.Value.Offset is not { } offset) return Failure("Use", "帧地址的起点不是常量。");
            int width = types.StorageBits(element!);
            if (width <= 0 || types.Kind(element!) is null or TypeKind.Void || element is ByRefRef) return Failure("Use", "帧对象缺少完整布局：" + element);
            var fields = element is DefinitionRef structure && types.Kind(element) == TypeKind.Struct
                ? types.Projections(structure).OrderBy(p => p.Bit).ToImmutableArray() : [];
            if (types.Kind(element!) == TypeKind.Struct)
            {
                int end = 0;
                foreach (var field in fields)
                {
                    if (!field.Fits(width) || field.Bit < end || field.Bit % 8 != 0 || field.Width % 8 != 0)
                        return Failure("Struct", "结构体帧对象的叶子范围不完整或相交：" + element);
                    end = field.Bit + field.Width;
                }
                if (fields.IsEmpty) return Failure("Struct", "结构体帧对象没有完整叶子布局：" + element);
            }
            var item = new FrameObject(native.Value with { Width = width }, element!, resolved.Value) { Fields = fields };
            if (objects.TryGetValue(offset, out var previous) && !previous.Type.Equals(element))
                return Failure("Mixed", "同一帧起点被取作不同类型：" + previous.Type + "、" + element);
            objects[offset] = item;
        }
        if (objects.Count == 0)
            return clearBuffers.Count > 0 ? Failure("Fill", "整帧清零缺少明确的托管类型见证。")
                : Outcome<FrameObjects>.Success(new([], ImmutableDictionary<StableIdentity, FrameAccess>.Empty)
                    { AddressSpills = spills.Keys.ToImmutableHashSet() });
        foreach (var (term, element) in uses)
        {
            var resolved = c.Get(state.Resolve, term); if (!resolved.IsSuccess) return resolved.Propagate<FrameObjects>();
            var addresses = c.Get(addressUses, term); if (!addresses.IsSuccess) return addresses.Propagate<FrameObjects>();
            foreach (var use in addresses.Value)
                if (use.Term != resolved.Value || use.Location.Offset is not { } offset || element is null
                    || !objects.TryGetValue(offset, out var item) || !item.Type.Equals(element))
                    return Failure("Use", "帧地址用于写入内存、普通实参或运算：" + string.Join("、", objects.Values.Select(o => o.Type).Distinct()));
        }
        var list = objects.Values.OrderBy(v => v.Storage.Offset).ToImmutableArray();
        // 地址溢出只在私有的未定型槽里转送；写进托管对象内容仍是地址逃逸。
        foreach (var spill in spills.Values)
            foreach (var item in list)
            {
                var overlap = c.Get(state.Alias, new(spill, item.Storage));
                if (!overlap.IsSuccess) return overlap.Propagate<FrameObjects>();
                if (overlap.Value.Kind != AliasKind.Disjoint) return Failure("Use", "帧地址溢出覆盖已认定的帧对象：" + item.Type);
            }
        // 入口栈实参已有调用方给定的初值，不能当成零初始化局部。
        if (c.Snapshot.IncomingArgumentArea is { } incoming)
            foreach (var piece in signature.Slots.Parameters.SelectMany(p => p.Pieces.Concat(p.CopyAddress is { } copy ? [copy] : []))
                .Where(p => p.Slot.Kind == SlotKind.ArgumentArea))
            {
                var area = c.Get(state.Locations, new(incoming, piece.Length * 8));
                if (!area.IsSuccess) return area.Propagate<FrameObjects>();
                var argument = area.Value with { Offset = area.Value.Offset + piece.Slot.Position + piece.SlotOffset };
                foreach (var item in list)
                {
                    var overlap = c.Get(state.Alias, new(argument, item.Storage));
                    if (!overlap.IsSuccess) return overlap.Propagate<FrameObjects>();
                    if (overlap.Value.Kind != AliasKind.Disjoint) return Failure("Use", "帧对象与入口栈实参重叠，缺少局部初值证明：" + item.Type);
                }
            }
        var fieldsOfObjects = new HashSet<FrameObject>();
        for (int i = 0; i < list.Length; i++)
            for (int j = 0; j < i; j++)
            {
                var overlap = c.Get(state.Alias, new(list[i].Storage, list[j].Storage));
                if (!overlap.IsSuccess) return overlap.Propagate<FrameObjects>();
                if (overlap.Value.Kind == AliasKind.Disjoint) continue;
                // 布局证明的完整字段属于外层局部；不能把相邻或部分相交的槽当作字段。
                if (overlap.Value.Kind == AliasKind.Overlap && overlap.Value.LeftLow == 0 && overlap.Value.Width == list[i].Storage.Width
                    && types.Kind(list[i].Type) != TypeKind.Struct && list[j].Type is DefinitionRef parent
                    && types.Project(parent, overlap.Value.RightLow, overlap.Value.Width) is { } field
                    && field.Bit == overlap.Value.RightLow && field.Width == overlap.Value.Width && field.Type.Equals(list[i].Type))
                { fieldsOfObjects.Add(list[i]); continue; }
                return Failure("Mixed", "已取址的帧对象范围相交：" + list[i].Type + "、" + list[j].Type);
            }
        list = list.Where(item => !fieldsOfObjects.Contains(item)).ToImmutableArray();
        var cleared = ImmutableDictionary.CreateBuilder<CallIdentity, FrameObject>();
        foreach (var (clear, pointer) in clearBuffers)
        {
            var resolved = c.Get(state.Resolve, pointer); if (!resolved.IsSuccess) return resolved.Propagate<FrameObjects>();
            var storage = c.Get(state.Locations, new(resolved.Value, clear.Length * 8));
            if (!storage.IsSuccess) return storage.Propagate<FrameObjects>();
            var item = list.SingleOrDefault(o => o.Storage == storage.Value);
            if (item is null) return Failure("Fill", "清零范围必须恰好覆盖一个已认定的帧对象。");
            cleared.Add(clear.Identity, item);
        }
        var results = ImmutableDictionary.CreateBuilder<CallIdentity, FrameObject>();
        foreach (var buffer in buffers)
        {
            var pointer = c.Get(state.Resolve, buffer.Pointer); if (!pointer.IsSuccess) return pointer.Propagate<FrameObjects>();
            var location = c.Get(state.Locations, new(pointer.Value, buffer.Length * 8)); if (!location.IsSuccess) return location.Propagate<FrameObjects>();
            if (location.Value.Region != Region.Frame)
            {
                var alternatives = c.Get(addressUses, buffer.Pointer); if (!alternatives.IsSuccess) return alternatives.Propagate<FrameObjects>();
                foreach (var alternative in alternatives.Value)
                    foreach (var item in list)
                    {
                        var alias = c.Get(state.Alias, new(alternative.Location with { Width = buffer.Length * 8 }, item.Storage));
                        if (!alias.IsSuccess) return alias.Propagate<FrameObjects>();
                        if (alias.Value.Kind != AliasKind.Disjoint)
                            return Failure("Struct", "结构体缓冲区的合流地址可能覆盖帧对象：" + item.Type);
                    }
                continue;
            }
            foreach (var item in list)
            {
                var overlap = c.Get(state.Alias, new(location.Value, item.Storage)); if (!overlap.IsSuccess) return overlap.Propagate<FrameObjects>();
                if (overlap.Value.Kind == AliasKind.Disjoint) continue;
                if (overlap.Value.Kind != AliasKind.Overlap || overlap.Value.LeftLow != 0 || overlap.Value.RightLow != 0
                    || overlap.Value.Width != item.Storage.Width || overlap.Value.Width != location.Value.Width || !buffer.Type.Equals(item.Type))
                    return Failure("Struct", "结构体缓冲区只部分覆盖帧对象或类型不相同：" + item.Type);
                if (buffer.Write) results.Add(buffer.Call, item);
            }
        }
        foreach (var buffer in buffers.Where(b => !b.Write))
        {
            var pointer = c.Get(state.Resolve, buffer.Pointer);
            if (!pointer.IsSuccess) return pointer.Propagate<FrameObjects>();
            var storage = c.Get(state.Locations, new(pointer.Value, buffer.Length * 8));
            if (!storage.IsSuccess) return storage.Propagate<FrameObjects>();
            if (storage.Value.Region != Region.Frame) continue;
            var item = list.Single(o => o.Storage == storage.Value);
            foreach (var field in item.Fields)
            {
                var value = c.Get(state.Reaching, new(buffer.Point, item.Storage with { Offset = item.Storage.Offset + field.Bit / 8, Width = field.Width }));
                if (!value.IsSuccess) return value.Propagate<FrameObjects>();
                if (value.Value.Bits.Any(bits => bits.Count != 1 || bits.Single().Value.Kind is TermKind.Unknown or TermKind.Undefined
                    || bits.Single().Value.Identity is MemoryAtom { Location.Region: Region.Frame, Definition: null }
                    || bits.Single().Value.Identity is MemoryAtom { Definition: CallIdentity call } && indirectInputs.Contains(call)))
                    return Outcome<FrameObjects>.Failure(new("lowering.IndirectArgument.Source", "间接实参的帧副本缺少全部叶子的初始化证明。"));
            }
        }
        var accesses = ImmutableDictionary.CreateBuilder<StableIdentity, FrameAccess>();
        if (list.IsEmpty) return Outcome<FrameObjects>.Success(new(list, accesses.ToImmutable()));
        foreach (var statement in c.Snapshot.Blocks.SelectMany(b => b.Statements))
        {
            var request = statement switch { MemoryRead r => new AddressRequest(r.Address, r.Width),
                MemoryWrite w => new AddressRequest(w.Address, w.Width), _ => default };
            if (request.Address is null) continue;
            var address = c.Get(state.Resolve, request.Address); if (!address.IsSuccess) return address.Propagate<FrameObjects>();
            var location = c.Get(state.Locations, new(address.Value, request.Width)); if (!location.IsSuccess) return location.Propagate<FrameObjects>();
            if (location.Value.Region != Region.Frame) continue;
            foreach (var item in list)
            {
                var overlap = c.Get(state.Alias, new(location.Value, item.Storage)); if (!overlap.IsSuccess) return overlap.Propagate<FrameObjects>();
                if (overlap.Value.Kind == AliasKind.Disjoint) continue;
                if (overlap.Value.Kind != AliasKind.Overlap || overlap.Value.LeftLow != 0 || overlap.Value.Width != request.Width)
                    return request.Width > 64 ? WideFailure(0, request.Width, "直接帧访问跨越对象边界：" + item.Type)
                        : Failure("Mixed", "直接帧访问跨越对象边界：" + item.Type);
                ImmutableArray<ValueProjection> parts;
                if (types.Kind(item.Type) == TypeKind.Struct)
                {
                    int start = overlap.Value.RightLow, end = start + request.Width;
                    parts = item.Fields.Where(f => f.Bit < end && f.Bit + f.Width > start).ToImmutableArray();
                    if (parts.Any(f => f.Bit < start || f.Bit + f.Width > end)
                        || parts.IsEmpty && !(statement is MemoryWrite && request.Width > 64))
                        return request.Width > 64 ? WideFailure(start, request.Width, "结构体帧访问只覆盖叶子的一部分：" + item.Type)
                            : Failure("Struct", "结构体帧访问只覆盖叶子的一部分或跨越字段：" + item.Type);
                }
                else
                {
                    if (overlap.Value.RightLow != 0 || request.Width != item.Storage.Width)
                        return Failure("Partial", "标量帧对象只支持完整宽度访问：" + item.Type);
                    parts = [new([], item.Type, 0, item.Storage.Width)];
                }
                var id = statement is MemoryRead read ? (StableIdentity)read.Identity : ((MemoryWrite)statement).Identity;
                if (statement is MemoryRead observed && indirectInputs.Count > 0)
                {
                    var at = index.Value.Reads[observed.Identity].Point;
                    var reaching = c.Get(state.Reaching, new(at, location.Value));
                    if (!reaching.IsSuccess) return reaching.Propagate<FrameObjects>();
                    if (reaching.Value.Bits.Any(bits => bits.Count != 1
                        || bits.Single().Value.Identity is MemoryAtom { Definition: CallIdentity call } && indirectInputs.Contains(call)))
                        return Outcome<FrameObjects>.Failure(new("lowering.IndirectArgument.Source", "帧副本在间接按值调用后被读取，调用可能改写的内容尚无托管写回来源。"));
                }
                accesses.Add(id, new(item, location.Value, parts));
            }
        }
        var copies = ImmutableDictionary.CreateBuilder<WriteIdentity, FrameCopy>();
        var remainders = ImmutableHashSet.CreateBuilder<WriteIdentity>();
        // 连续、不相交且铺满对象的写入共用整体值查询；其间不跨过任何其他内存操作。
        foreach (var block in c.Snapshot.Blocks)
            for (int i = 0; i < block.Statements.Length; i++)
            {
                if (block.Statements[i] is not MemoryWrite first || !accesses.TryGetValue(first.Identity, out var access)
                    || types.Kind(access.Object.Type) != TypeKind.Struct) continue;
                var group = new List<(MemoryWrite Write, FrameAccess Access)>(); int j = i;
                while (j < block.Statements.Length && block.Statements[j] is MemoryWrite write
                    && accesses.TryGetValue(write.Identity, out var next) && next.Object == access.Object && write.Width % 8 == 0)
                { group.Add((write, next)); j++; }
                var ordered = group.OrderBy(w => w.Access.Location.Offset).ToArray();
                var cursor = access.Object.Storage.Offset!.Value; bool complete = ordered.Length > 0;
                foreach (var part in ordered)
                {
                    if (part.Access.Location.Offset != cursor) { complete = false; break; }
                    cursor += part.Write.Width / 8;
                }
                if (complete && cursor * 8 == access.Object.Storage.Offset * 8 + access.Object.Storage.Width)
                {
                    var source = new PiecesSource([.. ordered.Select(w => new BoundPiece(
                        (int)(w.Access.Location.Offset!.Value - access.Object.Storage.Offset.Value), w.Write.Width / 8, new TermSource(w.Write.Value)))]);
                    copies.Add(first.Identity, new(access.Object, source, new(block.Identity, i)));
                    foreach (var rest in group.Skip(1)) remainders.Add(rest.Write.Identity);
                    i = j - 1;
                }
                else if (first.Width == access.Object.Storage.Width && access.Location.Offset == access.Object.Storage.Offset)
                    copies.Add(first.Identity, new(access.Object, new TermSource(first.Value), new(block.Identity, i)));
            }
        return Outcome<FrameObjects>.Success(new(list, accesses.ToImmutable()) { Results = results.ToImmutable(), Copies = copies.ToImmutable(),
            CopyRemainders = remainders.ToImmutable(), AddressSpills = spills.Keys.ToImmutableHashSet(), Clears = cleared.ToImmutable() });
    }
    private static Outcome<FrameObjects> Failure(string code, string message) => Outcome<FrameObjects>.Failure(new("lowering.Frame." + code, message));
    private static Outcome<FrameObjects> WideFailure(int low, int width, string message) =>
        Outcome<FrameObjects>.Failure(new("lowering.Wide.Layout", $"帧访问位段 [{low},{low + width})：{message}"));
}
