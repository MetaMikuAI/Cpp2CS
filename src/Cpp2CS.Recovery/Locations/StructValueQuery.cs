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
                if (key.Low % 8 != 0 || key.Width % 8 != 0 || key.Low + key.Width > stack.Length * 8) return Missing();
                return c.Get(sources, new(stack with { Offset = stack.Offset + key.Low / 8, Length = key.Width / 8 }, key.Point));
            case IndirectSource indirect:
                if (key.Low % 8 != 0 || key.Width % 8 != 0 || key.Low + key.Width > indirect.Length * 8) return Missing();
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
    private readonly ManagedRangeQuery? memoryRanges;
    private readonly FlowQueries flow = new();
    public StructPartQuery Parts { get; }
    public StructValueQuery(ManagedTypes types, StateQueries state, ManagedLocationQuery? locations, IEnumerable<StructOrigin> origins)
    {
        this.types = types; this.state = state; this.locations = locations; this.origins = origins.ToImmutableArray();
        ranges = new(state); sourcePointers = new(state); Parts = new(this);
        memoryRanges = locations is null ? null : new(locations, types);
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
            bool same = true;
            foreach (var leaf in parts)
            {
                var source = c.Get(ranges, new(origin.Source, origin.Point, leaf.Projection.Bit, leaf.Projection.Width));
                if (!source.IsSuccess) { same = false; break; }
                if (source.Value == leaf.Value) continue;
                var whole = WideMemory(leaf.Value) && types.StorageBits(structure) > 64
                    ? c.Get(ranges, new(origin.Source, origin.Point, leaf.Projection.Bit, leaf.Projection.Width, types.StorageBits(structure)))
                    : default;
                if (!whole.IsSuccess || whole.Value != leaf.Value) { same = false; break; }
            }
            if (same) return Outcome<StructPlan>.Success(new(origin, null, null, parts));
        }
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

    private Outcome<StructPlan?> MemoryCopy(QueryContext c, DefinitionRef type, ImmutableArray<StructLeaf> leaves, Point use)
    {
        Outcome<StructPlan?> None() => Outcome<StructPlan?>.Success(null);
        if (locations is null) return None();
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<StructPlan?>();
        LocationView? whole = null;
        var observations = new List<(Location Location, Term Atom, Point Point, MemoryRead Read)>();
        foreach (var leaf in leaves)
        {
            var term = leaf.Value; int low = 0;
            if (term.Kind == TermKind.Slice) { low = term.SliceLow!.Value; term = term.Operands[0]; }
            var memory = term.Identity switch { MemoryAtom atom => atom.Location, MemoryMerge merge => merge.Location, _ => null };
            if (memory is null) return None();
            // 读取身份来自快照索引；同值复用选择其中最早的原读取。
            (Point Point, MemoryRead Read)? observation = null;
            foreach (var read in index.Value.Reads.Values.OrderBy(r => r.Point.Before))
            {
                var source = c.Get(state.Read, read.Read.Identity);
                if (source.IsSuccess && source.Value == term
                    && c.Get(flow.PointDominates, new(read.Point, use)) is { IsSuccess: true, Value: true })
                { observation = read; break; }
            }
            if (observation is not { } observed) return None();
            var located = c.Get(locations, new(observed.Read.Address, observed.Read.Width));
            if (!located.IsSuccess) return located.Propagate<StructPlan?>();
            LocationView? candidate = null;
            foreach (var view in located.Value.Views.Where(v => v.Type.Equals(type)))
            {
                if (view.Offset * 8 + low != leaf.Projection.Bit || low + leaf.Projection.Width > term.Width) continue;
                // 路径末端是同类型的结构体位置，字段范围仍由公共投影给出。
                candidate = view with { Offset = 0, Width = types.StorageBits(type) }; break;
            }
            // 数组元素本身是结构体；定位查询的字段视图携带元素类型。
            if (candidate is null && located.Value.Views.FirstOrDefault(v => v.Kind == ManagedLocationKind.ArrayElement && Equals(v.ElementType, type)) is { } element)
            {
                var projection = types.Project(type, element.Path);
                if (projection is not null && projection.Bit + element.Offset * 8 + low == leaf.Projection.Bit)
                    candidate = element with { Type = type, Path = [], Offset = 0, Width = types.StorageBits(type) };
            }
            if (candidate is null && observed.Read.Width > 64)
            {
                var range = c.Get(memoryRanges!, new(observed.Read.Address, observed.Read.Width));
                if (!range.IsSuccess) return range.Propagate<StructPlan?>();
                candidate = range.Value.Aggregates.FirstOrDefault(p => p.View!.Type.Equals(type)
                    && p.AccessBit + leaf.Projection.Bit == low && low + leaf.Projection.Width <= p.AccessBit + p.Width)?.View;
            }
            if (candidate is null || whole is not null && !SameLocation(whole, candidate)) return None();
            whole ??= candidate;
            observations.Add((memory, term, observed.Point, observed.Read));
        }
        if (observations.Select(o => o.Point.Block).Distinct().Count() != 1) return None();
        var first = observations.MinBy(o => o.Point.Before);
        var last = observations.Max(o => o.Point.Before);
        var reads = observations.Select(o => o.Read.Identity).ToHashSet();
        if (index.Value.Blocks[first.Point.Block].Statements.Skip(first.Point.Before).Take(last - first.Point.Before + 1)
            .Any(s => s is Call or MemoryWrite || s is MemoryRead read && !reads.Contains(read.Identity))) return None();
        foreach (var observation in observations)
        {
            var value = c.Get(state.ValueAt, new(first.Point, observation.Location));
            if (!value.IsSuccess) return value.Propagate<StructPlan?>();
            if (value.Value != observation.Atom) return None();
        }
        return Outcome<StructPlan?>.Success(new(null, whole, first.Read.Identity, leaves));
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
            foreach (var origin in q.origins)
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
