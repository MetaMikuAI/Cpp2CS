using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Locations;

/// <summary>入口或调用定义的结构体整体；Point 是副本内容的定义时刻。</summary>
public sealed record StructOrigin(TypeRef Type, BoundSource Source, Point Point, int? Parameter = null, CallIdentity? Call = null);
public readonly record struct StructRequest(TypeRef Type, BoundSource Source, Point Point);
public sealed record StructLeaf(ValueProjection Projection, Term Value);
public sealed record StructPlan(StructOrigin? Origin, LocationView? Location, ReadIdentity? Read, ImmutableArray<StructLeaf> Leaves)
{
    public ValueProjection? Representation { get; init; }
}
public readonly record struct StructPartRequest(Term Term, int Low, int Width);
public sealed record StructPart(StructOrigin Origin, ValueProjection Projection, int Low, int Width);
internal readonly record struct SourceRange(BoundSource Source, Point Point, int Low, int Width, int UnitWidth = 0);

/// <summary>绑定值的位范围视图；填充不补零，间接内容只向状态模型查询。</summary>
internal sealed class SourceRangeQuery(StateQueries state) : Query<SourceRange, Term>
{
    private readonly BoundSourceQuery sources = new(state);
    public override Outcome<Term> Compute(QueryContext c, SourceRange key)
    {
        var t = c.Snapshot.Terms;
        if (key.UnitWidth > 0)
        {
            if (key.Low < 0 || (long)key.Low + key.Width > key.UnitWidth) return Missing();
            // 整体读取与逐字段读取的内存原子宽度不同；整段视图仍使用同一个定义时刻。
            var whole = c.Get(this, key with { Low = 0, Width = key.UnitWidth, UnitWidth = 0 });
            return whole.IsSuccess ? c.Get(state.Resolve, t.Slice(whole.Value, key.Low, key.Width)) : whole;
        }
        switch (key.Source)
        {
            case TermSource source:
                if (key.Low < 0 || key.Low + key.Width > source.Term.Width) return Missing();
                return c.Get(state.Resolve, t.Slice(source.Term, key.Low, key.Width));
            case StackSource stack:
                if (key.Low < 0 || key.Low % 8 != 0 || key.Width % 8 != 0 || key.Low + key.Width > stack.Length * 8) return Missing();
                return c.Get(sources, new(stack with { Offset = stack.Offset + key.Low / 8, Length = key.Width / 8 }, key.Point));
            case IndirectSource indirect:
                if (key.Low < 0 || key.Low % 8 != 0 || key.Width % 8 != 0 || key.Low + key.Width > indirect.Length * 8) return Missing();
                var pointer = c.Get(sources, new(indirect.Address, key.Point));
                if (!pointer.IsSuccess) return pointer;
                var resolved = c.Get(state.Resolve, pointer.Value); if (!resolved.IsSuccess) return resolved;
                var address = t.Apply(new CoreOperator(CoreOperation.Add), resolved.Value.Width, resolved.Value, t.Constant(key.Low / 8, resolved.Value.Width));
                var location = c.Get(state.Locations, new(address, key.Width)); if (!location.IsSuccess) return location.Propagate<Term>();
                return c.Get(state.ValueAt, new(key.Point, location.Value));
            case PiecesSource pieces:
                var parts = new List<Term>(); int cursor = key.Low;
                foreach (var piece in pieces.Pieces.OrderBy(p => p.ValueOffset))
                {
                    int low = Math.Max(key.Low, piece.ValueOffset * 8), end = Math.Min(key.Low + key.Width, (piece.ValueOffset + piece.Length) * 8);
                    if (low >= end) continue;
                    if (low != cursor) return Missing();
                    var value = c.Get(this, new(piece.Source, key.Point, low - piece.ValueOffset * 8, end - low));
                    if (!value.IsSuccess) return value;
                    parts.Add(value.Value); cursor = end;
                }
                return cursor == key.Low + key.Width ? c.Get(state.Resolve, t.Concat(parts.ToArray())) : Missing();
            default: return Missing();
        }
    }
    private static Outcome<Term> Missing() => Outcome<Term>.Failure(new("lowering.Struct.Incomplete", "结构体位片没有覆盖所需字段。"));
}

/// <summary>由字段投影核对整体来源；只用解析后的项相等与状态模型的读取版本，不猜测位置。</summary>
public sealed class StructValueQuery : Query<StructRequest, StructPlan>
{
    private readonly ManagedTypes types;
    private readonly StateQueries state;
    private readonly ManagedLocationQuery? locations;
    private readonly ImmutableArray<StructOrigin> origins;
    private readonly SourceRangeQuery ranges;
    internal SourceRangeQuery Ranges => ranges;
    private readonly BoundSourceQuery sourcePointers;
    private readonly FlowQueries flow = new();
    public StructPartQuery Parts { get; }
    public StructValueQuery(ManagedTypes types, StateQueries state, ManagedLocationQuery? locations, IEnumerable<StructOrigin> origins)
    {
        this.types = types; this.state = state; this.locations = locations; this.origins = origins.ToImmutableArray();
        ranges = new(state); sourcePointers = new(state); Parts = new(this);
    }
    public override Outcome<StructPlan> Compute(QueryContext c, StructRequest key)
    {
        if (key.Type is not DefinitionRef structure || types.Layouts.Of(structure) is null)
            return Failure("Layout", "结构体缺少封闭实例布局。");
        // ABI 的间接按值输入读取整个对象；求值点就是原调用处，不把内容转发过其他调用。
        if (locations?.Frames is { } frames && key.Source is IndirectSource indirect && indirect.Length * 8 == types.StorageBits(structure))
        {
            var pointer = c.Get(sourcePointers, new(indirect.Address, key.Point));
            if (!pointer.IsSuccess) return pointer.Propagate<StructPlan>();
            var resolved = c.Get(state.Resolve, pointer.Value); if (!resolved.IsSuccess) return resolved.Propagate<StructPlan>();
            var native = c.Get(state.Locations, new(resolved.Value, indirect.Length * 8)); if (!native.IsSuccess) return native.Propagate<StructPlan>();
            var view = frames.Locate(native.Value).Views.FirstOrDefault(v => v.Type.Equals(key.Type) && v.Offset == 0 && v.Path.IsEmpty);
            if (view is not null) return Outcome<StructPlan>.Success(new(null, view, null, []));
        }
        var projections = types.Projections(structure).OrderBy(p => p.Bit).ToArray();
        if (projections.Length == 0) return Failure("Layout", "结构体没有可证明的叶子字段。");
        int end = 0;
        foreach (var field in projections)
        {
            if (!field.Fits(types.StorageBits(structure))) return Failure("Layout", "结构体字段范围超出布局。");
            if (field.Bit < end) return Failure("Overlap", "结构体叶子字段重叠。");
            end = field.Bit + field.Width;
        }
        var leaves = ImmutableArray.CreateBuilder<StructLeaf>();
        foreach (var projection in projections)
        {
            var source = c.Get(ranges, new(key.Source, key.Point, projection.Bit, projection.Width));
            if (!source.IsSuccess) return source.Propagate<StructPlan>();
            if (Incomplete(source.Value)) return Failure("Incomplete", "结构体有字段包含未知或未定义位。");
            leaves.Add(new(projection, source.Value));
        }
        var parts = leaves.ToImmutable();
        foreach (var origin in origins.Where(o => o.Type.Equals(key.Type)))
        {
            if (origin.Point != key.Point && c.Get(flow.PointDominates, new(origin.Point, key.Point)) is not { IsSuccess: true, Value: true }) continue;
            var point = origin.Parameter is not null && origin.Source is IndirectSource ? key.Point : origin.Point;
            if (!SameLeaves(c, origin.Source, point, parts)) continue;
            return Outcome<StructPlan>.Success(new(origin with { Point = point }, null, null, parts));
        }
        if (parts.All(leaf => leaf.Value.ConstantValue == 0)) return Outcome<StructPlan>.Success(new(null, null, null, parts));
        var copy = MemoryCopy(c, structure, parts, key.Point);
        if (!copy.IsSuccess || copy.Value is not null) return copy.IsSuccess
            ? Outcome<StructPlan>.Success(copy.Value!) : copy.Propagate<StructPlan>();
        var fields = types.Fields(structure).ToArray();
        var representation = fields.Length == 1 && fields[0].Bit == 0 && fields[0].Width == types.StorageBits(structure) ? fields[0] : null;
        return Outcome<StructPlan>.Success(new(null, null, null, parts) { Representation = representation });
    }
    private static bool Incomplete(Term term) => term.Kind is TermKind.Undefined or TermKind.Unknown || term.Operands.Any(Incomplete);
    private static bool WideMemory(Term term)
    {
        var root = term.Kind == TermKind.Slice ? term.Operands[0] : term;
        return root.Width > 64 && root.Identity is MemoryAtom or MemoryMerge;
    }
    private static Outcome<StructPlan> Failure(string code, string text) => Outcome<StructPlan>.Failure(new("lowering.Struct." + code, text));

    // 用现场的读取粒度向 ValueAt 取对应位段；相等仍是项身份相等。
    private bool SameSource(QueryContext c, BoundSource source, Point point, int bit, Term value)
    {
        var ordinary = c.Get(ranges, new(source, point, bit, value.Width));
        if (ordinary.IsSuccess && ordinary.Value == value) return true;
        if (value.Kind == TermKind.Concat)
        {
            int offset = bit;
            foreach (var part in value.Operands)
            {
                if (!SameSource(c, source, point, offset, part)) return false;
                offset += part.Width;
            }
            return true;
        }
        var atom = value.Kind == TermKind.Slice ? value.Operands[0] : value;
        int low = value.Kind == TermKind.Slice ? value.SliceLow!.Value : 0;
        if (atom.Identity is not (MemoryAtom or MemoryMerge)) return false;
        var unit = c.Get(ranges, new(source, point, bit - low, atom.Width));
        if (!unit.IsSuccess && source is IndirectSource indirect && (bit - low) % 8 == 0)
        {
            var pointer = c.Get(sourcePointers, new(indirect.Address, point));
            if (pointer.IsSuccess && c.Get(state.Resolve, pointer.Value) is { IsSuccess: true } resolved)
            {
                var address = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), resolved.Value.Width, resolved.Value,
                    c.Snapshot.Terms.Constant(new System.Numerics.BigInteger((bit - low) / 8) & ((System.Numerics.BigInteger.One << resolved.Value.Width) - 1), resolved.Value.Width));
                var location = c.Get(state.Locations, new(address, atom.Width));
                if (location.IsSuccess) unit = c.Get(state.ValueAt, new(point, location.Value));
            }
        }
        if (!unit.IsSuccess) return false;
        var slice = c.Get(state.Resolve, c.Snapshot.Terms.Slice(unit.Value, low, value.Width));
        return slice.IsSuccess && slice.Value == value;
    }
    private bool SameLeaves(QueryContext c, BoundSource source, Point point, ImmutableArray<StructLeaf> leaves) =>
        leaves.All(leaf => SameSource(c, source, point, leaf.Projection.Bit, leaf.Value));

    private Outcome<StructPlan?> MemoryCopy(QueryContext c, DefinitionRef type, ImmutableArray<StructLeaf> leaves, Point use)
    {
        Outcome<StructPlan?> None() => Outcome<StructPlan?>.Success(null);
        if (locations is null) return None();
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<StructPlan?>();
        var observations = new List<(Point Point, MemoryRead Read, Term Address, LocationView View)>();
        // 从任一现场内存叶子发现候选；全部叶子的来源与时刻由 SameLeaves 一次核对。
        void Observe(Term value, int bit)
        {
            if (value.Kind == TermKind.Concat)
            {
                foreach (var part in value.Operands) { Observe(part, bit); bit += part.Width; }
                return;
            }
            foreach (var read in index.Value.Reads.Values)
            {
                if (read.Read.Width < value.Width || c.Get(flow.PointDominates, new(read.Point, use)) is not { IsSuccess: true, Value: true }
                    || c.Get(state.Read, read.Read.Identity) is not { IsSuccess: true } loaded) continue;
                for (int low = 0; low <= read.Read.Width - value.Width; low += 8)
                {
                    if ((bit - low) % 8 != 0 || c.Snapshot.Terms.Slice(loaded.Value, low, value.Width) != value) continue;
                    var address = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), read.Read.Address.Width,
                        read.Read.Address, c.Snapshot.Terms.Constant(new System.Numerics.BigInteger((low - bit) / 8) & ((System.Numerics.BigInteger.One << read.Read.Address.Width) - 1), read.Read.Address.Width));
                    var located = c.Get(locations, new(address, types.StorageBits(type)));
                    if (!located.IsSuccess) continue;
                    foreach (var view in located.Value.Views.Where(v => v.Type.Equals(type) && v.Offset == 0))
                        observations.Add((read.Point, read.Read, address, view));
                }
            }
        }
        foreach (var leaf in leaves) Observe(leaf.Value, leaf.Projection.Bit);
        var candidates = observations.DistinctBy(o => (o.Point, o.Address)).ToArray();
        foreach (var candidate in candidates)
        {
            var source = new IndirectSource(new TermSource(candidate.Address), types.Size(type));
            if (candidate.View.Kind == ManagedLocationKind.FrameLocal && SameLeaves(c, source, use, leaves))
                return Outcome<StructPlan?>.Success(new(null, candidate.View, null, leaves));
            // 字段与元素的隐含检查留在最早的原读取；不跨事件或提前退出下沉。
            if (candidates.Any(other => SameLocation(other.View, candidate.View) && other.Point != candidate.Point
                && c.Get(flow.PointDominates, new(other.Point, candidate.Point)) is { IsSuccess: true, Value: true })) continue;
            if (SameLeaves(c, source, candidate.Point, leaves))
                return Outcome<StructPlan?>.Success(new(null, candidate.View, candidate.Read.Identity, leaves));
        }
        return None();
    }

    private static bool SameLocation(LocationView a, LocationView b) => a.Kind == b.Kind && a.Root == b.Root && a.Index == b.Index
        && Equals(a.Type, b.Type) && a.Path.SequenceEqual(b.Path);

    public sealed class StructPartQuery(StructValueQuery q) : Query<StructPartRequest, StructPart?>
    {
        public override Outcome<StructPart?> Compute(QueryContext c, StructPartRequest key)
        {
            var desired = c.Get(q.state.Resolve, c.Snapshot.Terms.Slice(key.Term, key.Low, key.Width));
            if (!desired.IsSuccess) return desired.Propagate<StructPart?>();
            if (Incomplete(desired.Value)) return Outcome<StructPart?>.Success(null);
            // 间接形参可变；标量投影没有使用点，必须沿原读取快照下降。
            foreach (var origin in q.origins.Where(o => o.Parameter is null || o.Source is not IndirectSource))
            {
                if (origin.Type is not DefinitionRef structure) continue;
                foreach (var projection in q.types.Projections(structure))
                {
                    var source = c.Get(q.ranges, new(origin.Source, origin.Point, projection.Bit, projection.Width));
                    if (!source.IsSuccess) continue;
                    var whole = WideMemory(desired.Value) && q.types.StorageBits(structure) > 64
                        ? c.Get(q.ranges, new(origin.Source, origin.Point, projection.Bit, projection.Width, q.types.StorageBits(structure)))
                        : default;
                    var views = whole.IsSuccess
                        ? new[] { source.Value, whole.Value }
                        : [source.Value];
                    foreach (var view in views)
                    {
                        var part = view; int sourceLow = 0, desiredLow = 0;
                        if (part.Kind == TermKind.Slice) { sourceLow = part.SliceLow!.Value; part = part.Operands[0]; }
                        var value = desired.Value;
                        if (value.Kind == TermKind.Slice) { desiredLow = value.SliceLow!.Value; value = value.Operands[0]; }
                        if (part != value || desiredLow < sourceLow || desiredLow + key.Width > sourceLow + projection.Width) continue;
                        if (value.Width > 64 && value.Identity is MemoryAtom or MemoryMerge
                            && (desiredLow != sourceLow || key.Width != projection.Width))
                            return Outcome<StructPart?>.Failure(new("lowering.Wide.Layout",
                                $"宽读取的来源位段 [{desiredLow},{desiredLow + key.Width}) 只覆盖字段 {string.Join('.', projection.Path)} 的一部分。"));
                        return Outcome<StructPart?>.Success(new(origin, projection, desiredLow - sourceLow, key.Width));
                    }
                }
            }
            return Outcome<StructPart?>.Success(null);
        }
    }
}

/// <summary>ABI 间接结果缓冲区的完整片段写入；只消去确定落在结果区内的写入。</summary>
public sealed class StructReturnStoreQuery(StateQueries state, BoundSource pointer, int length) : Query<WriteIdentity, bool>
{
    private readonly BoundSourceQuery sources = new(state);
    public override Outcome<bool> Compute(QueryContext c, WriteIdentity key)
    {
        var write = c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Single(w => w.Identity == key);
        var output = c.Get(sources, new(pointer, new(c.Snapshot.Entry, 0))); if (!output.IsSuccess) return output.Propagate<bool>();
        var resolved = c.Get(state.Resolve, output.Value); if (!resolved.IsSuccess) return resolved.Propagate<bool>();
        var result = c.Get(state.Locations, new(resolved.Value, length * 8)); if (!result.IsSuccess) return result.Propagate<bool>();
        var address = c.Get(state.Resolve, write.Address); if (!address.IsSuccess) return address.Propagate<bool>();
        var target = c.Get(state.Locations, new(address.Value, write.Width)); if (!target.IsSuccess) return target.Propagate<bool>();
        var overlap = c.Get(state.Alias, new(target.Value, result.Value)); if (!overlap.IsSuccess) return overlap.Propagate<bool>();
        return Outcome<bool>.Success(overlap.Value.Kind == AliasKind.Overlap && overlap.Value.LeftLow == 0 && overlap.Value.Width == write.Width);
    }
}

public sealed record StructMemoryPart(LocationView View, Term Source, ImmutableArray<ReadIdentity> Reads)
{
    public int Low { get; init; }
    public int Width { get; init; }
}

/// <summary>宽读取中的完整标量字段；字段身份来自定位，快照保留所有等值原读取的求值点。</summary>
public sealed class StructMemoryPartQuery(StateQueries state, ManagedLocationQuery? locations, ManagedTypes types)
    : Query<StructPartRequest, StructMemoryPart?>
{
    private readonly ManagedRangeQuery? ranges = locations is null ? null : new(locations, types);
    private readonly ManagedReadSnapshotQuery placement = new(state);
    public override Outcome<StructMemoryPart?> Compute(QueryContext c, StructPartRequest key)
    {
        Outcome<StructMemoryPart?> None() => Outcome<StructMemoryPart?>.Success(null);
        if (locations is null) return None();
        var desired = c.Get(state.Resolve, c.Snapshot.Terms.Slice(key.Term, key.Low, key.Width));
        if (!desired.IsSuccess) return desired.Propagate<StructMemoryPart?>();
        if (desired.Value.Kind != TermKind.Slice || desired.Value.SliceLow!.Value % 8 != 0
            || desired.Value.Operands[0].Identity is not (MemoryAtom { Location.Region: Region.Other or Region.Frame }
                or MemoryMerge { Location.Region: Region.Frame })) return None();
        var source = desired.Value.Operands[0];
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<StructMemoryPart?>();
        var reads = ImmutableArray.CreateBuilder<ReadIdentity>(); LocationView? field = null;
        foreach (var observed in index.Value.Reads.Values)
        {
            var value = c.Get(state.Read, observed.Read.Identity);
            if (!value.IsSuccess || value.Value != source) continue;
            if (observed.Read.Width > 64)
            {
                var range = c.Get(ranges!, new(observed.Read.Address, observed.Read.Width));
                if (!range.IsSuccess) return range.Propagate<StructMemoryPart?>();
                if (range.Value.Kind == ManagedLocationKind.Unknown)
                    return Outcome<StructMemoryPart?>.Failure(new("lowering.Wide.Layout",
                        $"宽读取的来源范围 [0,{observed.Read.Width}) 没有完整布局。", range.Value.Why));
            }
            if (field is null)
            {
                var t = c.Snapshot.Terms;
                var address = t.Apply(new CoreOperator(CoreOperation.Add), observed.Read.Address.Width, observed.Read.Address,
                    t.Constant(desired.Value.SliceLow.Value / 8, observed.Read.Address.Width));
                var located = c.Get(locations, new(address, key.Width)); if (!located.IsSuccess) return located.Propagate<StructMemoryPart?>();
                var fields = located.Value.Views.Where(v => v.Offset == 0 && types.Kind(v.Type) is not (TypeKind.Struct or null)
                    && types.StorageBits(v.Type) == key.Width).ToArray();
                if (fields.Length != 1) break;
                field = fields[0];
            }
            reads.Add(observed.Read.Identity);
        }
        if (field is not null) return Outcome<StructMemoryPart?>.Success(new(field, source, reads.ToImmutable()));
        if (source.Identity is not MemoryAtom { Location.Region: Region.Other } memory) return None();
        // 写入转发和规范化可以只留下旧读取的部分位；在原读取的范围表里寻找保留这些位的标量位置。
        foreach (var observed in index.Value.Reads.Values)
        {
            var address = c.Get(state.Resolve, observed.Read.Address); if (!address.IsSuccess) continue;
            var native = c.Get(state.Locations, new(address.Value, observed.Read.Width)); if (!native.IsSuccess) continue;
            var overlap = c.Get(state.Alias, new(memory.Location, native.Value)); if (!overlap.IsSuccess) continue;
            int low = desired.Value.SliceLow!.Value;
            if (overlap.Value.Kind != AliasKind.Overlap || low < overlap.Value.LeftLow
                || low + key.Width > overlap.Value.LeftLow + overlap.Value.Width) continue;
            int readLow = low - overlap.Value.LeftLow + overlap.Value.RightLow;
            var value = c.Get(state.Read, observed.Read.Identity); if (!value.IsSuccess) continue;
            var slice = c.Get(state.Resolve, c.Snapshot.Terms.Slice(value.Value, readLow, key.Width));
            if (!slice.IsSuccess || slice.Value != desired.Value) continue;
            var dominates = c.Get(placement, new(observed.Read.Identity, source));
            if (!dominates.IsSuccess || !dominates.Value) continue;
            var range = c.Get(ranges!, new(observed.Read.Address, observed.Read.Width)); if (!range.IsSuccess) continue;
            var parts = range.Value.Pieces.Where(p => p.View is not null && readLow >= p.AccessBit
                && readLow + key.Width <= p.AccessBit + p.Width).ToArray();
            if (parts.Length != 1) continue;
            var part = parts[0];
            if (observed.Read.Width > 64 && (part.AccessBit != readLow || part.LocationBit != 0
                || part.Width != key.Width || key.Width != types.StorageBits(part.View!.Type)))
                return Outcome<StructMemoryPart?>.Failure(new("lowering.Wide.Layout",
                    $"宽读取的来源位段 [{readLow},{readLow + key.Width}) 只覆盖字段 {string.Join('.', part.View!.Path)} 的一部分。"));
            return Outcome<StructMemoryPart?>.Success(new(part.View!, value.Value, [observed.Read.Identity])
            { Low = part.LocationBit + readLow - part.AccessBit, Width = key.Width });
        }
        return None();
    }
}
