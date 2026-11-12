using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Locations;

public enum ManagedLocationKind { FrameLocal, InstanceField, ArrayElement, ArrayLength, StaticField, Indirect, NotManaged, Unknown }
/// <summary>Offset 是路径末端内的字节偏移，Width 是位宽；Type 为字段或元素类型，长度位置则为数组类型。Basis 保留签名或规格依据。</summary>
public sealed record LocationView(ManagedLocationKind Kind, Term Root, TypeRef Type,
    ImmutableArray<FieldRef> Path, BigInteger Offset, int Width, Term? Index, ValueName? Basis, TypeRef? ElementType = null);
public sealed record LocationResult(ManagedLocationKind Kind, ImmutableArray<LocationView> Views, Reason? Why = null);
public sealed record StaticValueType(TypeRef Type, ValueName? Basis);

/// <summary>函数级只读查询。通过 CreateContext 使用，命名、位置与读取类型共享显式不动点组。</summary>
public sealed class ManagedLocationQuery : Query<AddressRequest, LocationResult>
{
    internal readonly StateQueries State;
    internal readonly ValueNamingQuery Names;
    internal readonly ITypeLayouts Layouts;
    private readonly RuntimeSpec spec;
    internal readonly FrameObjects? Frames;
    public LocationTypeQuery Types { get; }
    public ManagedAddressQuery Addresses { get; }
    internal ManagedReadTypeQuery ReadTypes { get; }
    public ManagedLocationQuery(StateQueries state, ValueNamingQuery names, ITypeLayouts layouts, RuntimeSpec spec, FrameObjects? frames = null)
    {
        State = state; Names = names; Layouts = layouts; this.spec = spec; Frames = frames; Types = new(this); ReadTypes = new(this); Addresses = new(this);
        names.UseLocations(this);
    }
    public QueryContext CreateContext(NativeFunction function) => new(function, null, State.Group,
        new FixedPointGroup(1_000_000, [.. Names.Members, FixedPointMember.Create(this, _ => new LocationLattice()),
            FixedPointMember.Create(Types, _ => new TypeLattice()), FixedPointMember.Create(ReadTypes, _ => new TypeLattice())]));
    internal static LocationResult Pending { get; } = new(ManagedLocationKind.Unknown, [], new("location.pending", "循环尚无定位依据。"));
    internal static Outcome<LocationResult> Unknown(string code, string text) => Outcome<LocationResult>.Success(new(ManagedLocationKind.Unknown, [], new("location." + code, text)));
    private static Outcome<LocationResult> NotManaged(string reason) => Outcome<LocationResult>.Success(new(ManagedLocationKind.NotManaged, [], new("location.not-managed", reason)));
    public override Outcome<LocationResult> Compute(QueryContext c, AddressRequest key) => Locate(c, key, false);
    internal Outcome<LocationResult> Locate(QueryContext c, AddressRequest key, bool addressView)
    {
        var resolved = c.Get(State.Resolve, key.Address); if (!resolved.IsSuccess) return resolved.Propagate<LocationResult>();
        var address = resolved.Value;
        var location = c.Get(State.Locations, new(address, key.Width)); if (!location.IsSuccess) return location.Propagate<LocationResult>();
        if (location.Value.Region == Region.Frame && Frames is not null)
        {
            var frame = Frames.Locate(location.Value);
            if (!frame.Views.IsEmpty) return Outcome<LocationResult>.Success(frame);
        }
        if (location.Value.Region is Region.Frame or Region.Image)
            return NotManaged(location.Value.Region + (location.Value.Offset is null ? "：地址不是常量偏移" : "：常量偏移，宽 " + key.Width));
        if (location.Value.Region == Region.Thread) return Unknown("thread-static", "线程区域尚不定位。");
        var runtimeField = c.Get(Names.SpecificationReads, new(Names, location.Value));
        if (runtimeField.IsSuccess && runtimeField.Value == NameLattice.Pending) return Outcome<LocationResult>.Success(Pending);
        if (runtimeField.IsSuccess && (runtimeField.Value.Name is BitStorageName || runtimeField.Value.Name is FieldName specification &&
            specification.Field != spec.Layout.Field("Il2CppArray", "max_length").Path))
            return NotManaged("已命名的运行时结构字段：" + Describe(runtimeField.Value.Name));
        var terms = new List<Term>(); BigInteger offset = 0;
        var pending = new Stack<Term>(); pending.Push(address);
        while (pending.TryPop(out var term))
        {
            if (c.Step() is { } why) return Outcome<LocationResult>.Failure(why);
            if (term.ConstantValue is { } n) offset += n;
            else if (term.Operator is CoreOperator { Operation: CoreOperation.Add })
                foreach (var child in term.Operands) pending.Push(child);
            else if (term.Operator is CoreOperator { Operation: CoreOperation.Subtract } && term.Operands[1].ConstantValue is { } sub)
            { offset -= sub; pending.Push(term.Operands[0]); }
            else terms.Add(term);
        }
        var modulus = BigInteger.One << address.Width;
        offset = (offset % modulus + modulus) % modulus;
        if (offset >= modulus / 2) offset -= modulus;
        bool awaitingType = false, namedBase = false;
        string? baseKind = null;
        Reason? typeFailure = null, baseFailure = null;
        foreach (var root in terms)
        {
            var named = c.Get(Names, root);
            namedBase |= named.IsSuccess && named.Value.Name is not null;
            if (named.IsSuccess && named.Value.Name is { } baseName) baseKind ??= Describe(baseName);
            baseFailure ??= named.IsSuccess ? named.Value.Why : named.Why;
            if (named.IsSuccess && named.Value.Name is FieldName field && field.Record == "Il2CppClass")
            {
                if (field.Field == spec.Layout.Field("Il2CppClass", "thread_static_fields_offset").Path)
                    return Unknown("thread-static", "线程静态字段尚不定位。");
                if (field.Field == spec.Layout.Field("Il2CppClass", "static_fields").Path &&
                    field.Owner is EntityName { Entity: ClassEntity { Type: DefinitionRef owner } })
                    return terms.Count == 1 ? Fields(root, owner, offset, key.Width, true, false, field, addressView: addressView) : Unknown("index", "静态字段偏移不是常量。");
            }
            var typed = c.Get(Types, root);
            if (!typed.IsSuccess)
            {
                for (var why = typed.Why; why is not null; why = why.Cause)
                    if (why.Code is "location.merge-type" or "query.fixed-point") typeFailure = why;
                continue;
            }
            if (typed.Value is not { } value) { awaitingType = true; continue; }
            var type = value.Type;
            if (Open(type) && !(Layouts is Binding.GenericWitness witness && witness.Knows(type))) return Unknown("open-type", "开放类型没有实例布局。");
            if (type is ArrayRef array)
            {
                var length = spec.Layout.Field("Il2CppArray", "max_length");
                if (terms.Count == 1 && offset == length.ByteOffset && key.Width <= length.Size * 8)
                    return Yes(new(ManagedLocationKind.ArrayLength, root, type, [], 0, key.Width, null, value.Basis));
                if (!array.IsVector || array.Rank != 1) return Unknown("array-rank", "仅定位向量元素。");
                var size = Layouts.TrySizeAndAlignment(array.Element)?.Size;
                if (size is null or <= 0) return Unknown("layout", "元素大小不可用。");
                var relative = offset - spec.Layout.ArrayDataStart;
                if (terms.Count == 1 && relative < 0)
                {
                    return runtimeField.IsSuccess && runtimeField.Value.Name is FieldName or BitStorageName
                        ? NotManaged("已命名的数组头字段。") : Unknown("no-field", "偏移位于数组头，未对应长度或已命名规格字段。");
                }
                var remainder = (relative % size.Value + size.Value) % size.Value;
                var constantIndex = (relative - remainder) / size.Value;
                Term index = c.Snapshot.Terms.Constant(constantIndex & (modulus - 1), address.Width);
                foreach (var part in terms.Where((_, i) => i != terms.IndexOf(root)))
                {
                    if (part == root) return Unknown("index", "地址包含重复的数组基值。");
                    var unscaled = Unscale(c.Snapshot.Terms, part, size.Value);
                    if (unscaled is null) return Unknown("index", "字节偏移不能还原为元素下标。");
                    var indexType = c.Get(Types, unscaled);
                    if (indexType.IsSuccess && indexType.Value is { } knownIndex && (ManagedTypes.IsReferenceType(knownIndex.Type) || knownIndex.Type is ByRefRef))
                        return Unknown("index", "地址含多个托管基值，不能确定元素下标。");
                    index = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), address.Width, index, unscaled);
                }
                if (remainder * 8 + key.Width > size.Value * 8) return Unknown("cross-field", "访问跨越数组元素。");
                if (array.Element is DefinitionRef { Definition.IsValueType: true } element && ManagedTypes.PrimitiveName(element) is null && !element.Definition.IsEnum)
                    return Fields(root, element, remainder, key.Width, false, true, value.Basis, index, array.Element, addressView);
                return Yes(new(ManagedLocationKind.ArrayElement, root, array.Element, [], remainder, key.Width, index, value.Basis, array.Element));
            }
            if (type is ByRefRef cell && (ManagedTypes.IsReferenceType(cell.Element) || ManagedTypes.PrimitiveName(ManagedTypes.Underlying(cell.Element)) is not null))
            {
                var size = Layouts.TrySizeAndAlignment(cell.Element)?.Size;
                if (size is null) return Unknown("layout", "托管地址所指单元的大小不可用。");
                if (terms.Count != 1) return Unknown("index", "托管地址所指单元不支持变动偏移。");
                if (offset < 0 || offset * 8 + key.Width > size * 8) return Unknown("cross-field", "访问跨越托管地址所指单元。");
                return Yes(new(ManagedLocationKind.Indirect, root, cell.Element, [], offset, key.Width, null, value.Basis));
            }
            bool unboxed = type is ByRefRef;
            if (type is ByRefRef byref) type = byref.Element;
            if (type is DefinitionRef definition && (unboxed || !definition.Definition.IsValueType))
            {
                if (terms.Count != 1) return Unknown("index", "实例字段偏移不是常量。");
                if (definition.Definition.IsInterface || definition.Definition is { Assembly: "mscorlib.dll", FullName: "System.Object" })
                    return Unknown("static-type", "静态类型不足以定位字段，不猜派生类型。");
                var result = Fields(root, definition, offset, key.Width, false, unboxed, value.Basis, addressView: addressView);
                if (result.Value.Kind != ManagedLocationKind.Unknown) return result;
                if (runtimeField.IsSuccess && runtimeField.Value.Name is FieldName or BitStorageName) return NotManaged("已命名的运行时结构字段：" + Describe(runtimeField.Value.Name));
                return result;
            }
        }
        if (awaitingType) return Outcome<LocationResult>.Success(Pending);
        if (runtimeField.IsSuccess && runtimeField.Value.Name is FieldName or BitStorageName) return NotManaged("已命名的运行时结构字段：" + Describe(runtimeField.Value.Name));
        if (typeFailure is not null) return Outcome<LocationResult>.Success(new(ManagedLocationKind.Unknown, [], typeFailure));
        return Outcome<LocationResult>.Success(new(ManagedLocationKind.Unknown, [], new(namedBase ? "location.base-untyped" : "location.base-unnamed",
            namedBase ? "已命名基值没有静态类型：" + baseKind : "基值未命名。", baseFailure)));
    }
    // 洞的消息里写明名字的种类，报告才能按种类归并。
    private static string Describe(ValueName? name) => name switch
    {
        FieldName field => field.Record + "." + field.Field,
        BitStorageName bits => bits.Record + "." + bits.Fields,
        CallResultName result => "调用结果" + (result.Operation is { } operation ? "（" + operation + "）" : ""),
        EntityName entity => "元数据实体 " + entity.Entity.GetType().Name,
        ParameterName parameter => parameter.MethodInformation ? "方法信息形参" : "形参",
        null => "无",
        _ => name.GetType().Name,
    };
    private static bool Open(TypeRef type) => type switch
    {
        GenericParameterRef => true,
        DefinitionRef d => d.Definition.GenericParameters.Count != d.Arguments.Count || d.Arguments.Any(Open),
        ArrayRef a => Open(a.Element), ByRefRef r => Open(r.Element), PointerRef p => Open(p.Element), _ => false
    };
    private static Term? Unscale(TermTable terms, Term term, int size)
    {
        if (size == 1) return term;
        if (term.Operator is CoreOperator { Operation: CoreOperation.ShiftLeft } && term.Operands[1].ConstantValue is { } shift && shift >= 0 && shift < term.Width && (BigInteger.One << (int)shift) == size) return term.Operands[0];
        if (term.Operator is CoreOperator { Operation: CoreOperation.Multiply })
        {
            if (term.Operands[0].ConstantValue == size) return term.Operands[1];
            if (term.Operands[1].ConstantValue == size) return term.Operands[0];
        }
        // 常量左移在项表里规范成低位补零；恢复来源位片，保留窄运算的截断。
        if ((size & (size - 1)) == 0 && term.Kind == TermKind.Concat && term.Operands[0].ConstantValue == 0)
        {
            int bits = BitOperations.TrailingZeroCount((uint)size);
            if (term.Operands[0].Width < bits) return null;
            var index = terms.Slice(term, bits, term.Width - bits);
            if (index.Kind == TermKind.Slice && index.SliceLow == 0 && index.Operands[0].Width == term.Width) return index.Operands[0];
            if (index.Operator is CoreOperator { Operation: CoreOperation.SignExtend })
                return terms.Apply(new CoreOperator(CoreOperation.SignExtend), term.Width, index.Operands[0]);
            return terms.Apply(new CoreOperator(CoreOperation.ZeroExtend), term.Width, index);
        }
        return null;
    }
    private static Outcome<LocationResult> Yes(LocationView view) => Outcome<LocationResult>.Success(new(view.Kind, [view]));
    private Outcome<LocationResult> Fields(Term root, DefinitionRef type, BigInteger offset, int width,
        bool statics, bool unboxed, ValueName? basis, Term? index = null, TypeRef? element = null, bool addressView = false)
    {
        if (Open(type) && !(Layouts is Binding.GenericWitness witness && witness.Knows(type))) return Unknown("open-type", "开放类型没有实例布局。");
        var views = ImmutableArray.CreateBuilder<LocationView>(); bool crossing = false, missingLayout = false;
        // 数组元素和托管地址本身也是结构体位置，不要求访问恰好落在某个直接字段内。
        if (unboxed && !statics && offset == 0 && Layouts.Of(type) is { } rootLayout && (addressView || width == rootLayout.ValueSize * 8))
            views.Add(new(index is not null ? ManagedLocationKind.ArrayElement : ManagedLocationKind.Indirect,
                root, type, [], 0, width, index, basis, element));
        var work = new Stack<(DefinitionRef Type, BigInteger Offset, bool Static, bool Unboxed, ImmutableArray<FieldRef> Path)>();
        work.Push((type, offset, statics, unboxed, []));
        while (work.TryPop(out var item))
        {
            var layout = Layouts.Of(item.Type); if (layout is null) { missingLayout = true; continue; }
            var adjusted = item.Offset + (item.Unboxed ? layout.ObjectHeaderSize : 0);
            foreach (var slot in item.Static ? layout.Statics : layout.Fields)
            {
                var size = Layouts.TrySizeAndAlignment(slot.Type)?.Size;
                if (size is null) { missingLayout = true; continue; }
                var relative = adjusted - slot.Offset;
                if (relative < 0 || relative >= size) continue;
                if (relative * 8 + width > size * 8) { crossing = true; continue; }
                var path = item.Path.Add(new FieldRef(slot.Field, item.Type));
                var kind = index is not null ? ManagedLocationKind.ArrayElement : statics ? ManagedLocationKind.StaticField : ManagedLocationKind.InstanceField;
                views.Add(new(kind, root, slot.Type, path, relative, width, index, basis, element));
                if (slot.Type is DefinitionRef { Definition.IsValueType: true } nested && ManagedTypes.PrimitiveName(nested) is null && !nested.Definition.IsEnum)
                    work.Push((nested, relative, false, true, path));
            }
            if (!item.Static && !item.Type.Definition.IsValueType && item.Type.Definition.BaseType?.Substitute(item.Type.Arguments, []) is DefinitionRef parent)
                work.Push((parent, item.Offset, false, false, item.Path));
        }
        if (views.Count == 0) return Unknown(missingLayout ? "layout" : crossing ? "cross-field" : "no-field", missingLayout ? "布局不可用。" : crossing ? "访问跨字段。" : "偏移不落在字段上。");
        return Outcome<LocationResult>.Success(new(views[0].Kind, views.ToImmutable()));
    }
}

internal sealed class LocationLattice : ILattice<LocationResult>
{
    public LocationResult Bottom => ManagedLocationQuery.Pending;
    private static bool Same(LocationResult a, LocationResult b) => a.Kind == b.Kind && a.Why == b.Why && a.Views.Length == b.Views.Length && a.Views.Zip(b.Views).All(p =>
        p.First with { Path = p.Second.Path } == p.Second && p.First.Path.SequenceEqual(p.Second.Path));
    private bool Top(LocationResult value) => value.Kind == ManagedLocationKind.Unknown && value != Bottom;
    public LocationResult Join(LocationResult a, LocationResult b) => a == Bottom ? b : b == Bottom || Same(a, b) || Top(a) ? a : Top(b) ? b : new(ManagedLocationKind.Unknown, [], new("location.conflict", "循环定位不一致。"));
    public bool LessOrEqual(LocationResult a, LocationResult b) => a == Bottom || Same(a, b) || Top(b);
}
internal sealed class TypeLattice : ILattice<StaticValueType?>
{
    public StaticValueType? Bottom => null;
    public StaticValueType? Join(StaticValueType? a, StaticValueType? b) => a ?? b;
    public bool LessOrEqual(StaticValueType? a, StaticValueType? b) => a is null || b is not null && a.Type == b.Type;
}
public sealed class LocationTypeQuery(ManagedLocationQuery q) : Query<Term, StaticValueType?>
{
    public override Outcome<StaticValueType?> Compute(QueryContext c, Term key)
    {
        Outcome<StaticValueType?> Yes(StaticValueType? value) => Outcome<StaticValueType?>.Success(value);
        // 空位型本身不约束类型；合流的其他来源提供引用或整数类型。
        if (key.ConstantValue == 0) return Yes(null);
        var named = c.Get(q.Names, key);
        if (named.IsSuccess)
        {
            var type = named.Value.StaticType;
            if (type is not null) return Yes(new(type, named.Value.Name));
        }
        var resolved = c.Get(q.State.Resolve, key); if (!resolved.IsSuccess) return resolved.Propagate<StaticValueType?>();
        if (resolved.Value != key) return c.Get(this, resolved.Value);
        IEnumerable<Term>? inputs = null;
        if (key.Identity is ResultAtom { Definition: MergeIdentity id }) inputs = c.Snapshot.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == id).Inputs.Select(i => i.Value);
        if (key.Identity is MemoryMerge merge)
        { var edges = c.Get(q.State.MergeInputs, merge); if (!edges.IsSuccess) return edges.Propagate<StaticValueType?>(); inputs = edges.Value.Select(e => e.Value); }
        if (inputs is not null)
        {
            StaticValueType? common = null;
            foreach (var input in inputs)
            {
                var value = c.Get(this, input); if (!value.IsSuccess) return value;
                if (value.Value is null) continue;
                if (common is not null && common.Type != value.Value.Type) return Outcome<StaticValueType?>.Failure(new("location.merge-type", "合流来源类型不一致。"));
                common = value.Value with { Basis = null };
            }
            return Yes(common);
        }
        if (key.Identity is MemoryAtom memory)
        {
            var request = ManagedReadTypeQuery.Address(c, memory.Location);
            if (request is not null) return c.Get(q.ReadTypes, request.Value);
        }
        return Outcome<StaticValueType?>.Failure(new("location.base-type", "定义没有静态类型。"));
    }
}

/// <summary>完整托管读取的声明类型按地址与宽度缓存；读取版本仍由值名字保留。</summary>
internal sealed class ManagedReadTypeQuery(ManagedLocationQuery q) : Query<AddressRequest, StaticValueType?>
{
    internal static AddressRequest? Address(QueryContext c, Location location, int byteOffset = 0)
    {
        var address = location.UnknownOffsetAddress;
        if (location.Offset is { } offset)
            address = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), location.Root.Width, location.Root,
                c.Snapshot.Terms.Constant(offset & ((BigInteger.One << location.Root.Width) - 1), location.Root.Width));
        if (address is null) return null;
        if (byteOffset != 0) address = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), address.Width, address,
            c.Snapshot.Terms.Constant(byteOffset, address.Width));
        return new(address, location.Width);
    }
    public override Outcome<StaticValueType?> Compute(QueryContext c, AddressRequest key)
    {
        var location = c.Get(q, key); if (!location.IsSuccess) return location.Propagate<StaticValueType?>();
        if (location.Value == ManagedLocationQuery.Pending) return Outcome<StaticValueType?>.Success(null);
        var exact = location.Value.Views.Where(v => v.Kind != ManagedLocationKind.ArrayLength && v.Offset == 0 &&
            q.Layouts.TrySizeAndAlignment(v.Type)?.Size * 8 == key.Width).ToArray();
        // 同宽的包装结构体与它的标量叶子共享位型：读取取标量的类型，整体的使用另由结构体值查询取证。
        var leaves = exact.Where(v => ManagedTypes.IsReferenceType(v.Type) || v.Type is ByRefRef or PointerRef || ManagedTypes.IsNativePointer(v.Type) ||
            ManagedTypes.PrimitiveName(ManagedTypes.Underlying(v.Type)) is not null).ToArray();
        var types = (leaves.Length == 0 ? exact : leaves).Select(v => v.Type).Distinct().ToArray();
        if (types.Length == 1) return Outcome<StaticValueType?>.Success(new(types[0], null));
        return Outcome<StaticValueType?>.Failure(new("location.read-type", "读取没有唯一完整位置类型。", location.Value.Why));
    }
}
