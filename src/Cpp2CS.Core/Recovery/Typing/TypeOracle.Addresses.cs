using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

/// <summary>
/// 不落在单一实体上的地址值：fixed 取得的首元素指针、合流的位置地址、数组上的指针游标。
/// 它们都是 clang 优化后的形态，IL 中分别对应 fixed 语句、栈上合流的托管指针和按下标的元素访问。
/// </summary>
public sealed partial class TypeOracle
{
    /// <summary>
    /// fixed (T* p = array) 的首元素指针：长度为零时为空指针，否则为首元素地址。
    /// 空数组引用由读取长度时的判空排除，长度的读取仍要写出（见 <see cref="TypeUseAnalysis"/>）。
    /// </summary>
    public (Sym Array, ArrayRef Type)? PinnedArray(OpSym select)
    {
        if (select is not { Op.Kind: OperatorKind.Select, Width: 64, Args: [var condition, var empty, var data] }
            || SymTable.Resolve(empty) is not ConstSym { Value: 0 }
            || SymTable.Resolve(condition) is not OpSym { Op: { Kind: OperatorKind.Compare, Cond: Cond.Eq }, Args: [var length, var zero] }
            || SymTable.Resolve(zero) is not ConstSym { Value: 0 }) return null;
        var (root, offset, index, _) = Decompose(data);
        if (offset != RuntimeLayout.ArrayData || index is not null || TypeOf(root) is not ArrayRef { IsVector: true } array
            || !types.Unmanaged(array.Element)) return null;
        var bits = SymTable.Resolve(length) is SliceSym { Low: 0, Base: var whole } ? SymTable.Resolve(whole) : SymTable.Resolve(length);
        return bits is ReadSym read && Decompose(read.Address) is (var owner, RuntimeLayout.ArrayMaxLength, null, _)
            && ReferenceEquals(SymTable.Resolve(owner), SymTable.Resolve(root)) ? (root, array) : null;
    }

    /// <summary>路径拆分期间不把合流的地址当作托管指针：能拆分时各路径各自访问单一实体。</summary>
    public bool MergedAddresses { get; set; } = true;

    /// <summary>
    /// 来源都是位置地址的 φ 是托管指针：IL 把位置的地址留在栈上跨分支合流，或 clang 把不同路径上的同构访问下沉成一次经 φ 的访问。
    /// 指向的类型取各来源从外到内的位置类型中第一个共同的。常量零是从未被访问的栈合流初值，只作为空指针保留。
    /// </summary>
    private TypeRef? AddressMerge(PhiSym phi)
    {
        if (!MergedAddresses || phi.Width != 64 || phi.Projection is not null || phi.Sources.Any(s => s is null)) return null;
        var arms = new List<Sym>();
        for (var edge = 0; edge < phi.Sources.Length; edge++)
        {
            var source = EdgeSource(phi, edge);
            if (ReferenceEquals(source, phi) || source is ConstSym { Value: 0 }) continue;
            if (source is OpSym { Op.Kind: OperatorKind.Select, Args: [_, var first, var second] })
            {
                // 选择的一路是空指针时，托管指针与空指针不能在栈上合流。
                if (SymTable.IsZero(first) || SymTable.IsZero(second)) return null;
                arms.Add(SymTable.Resolve(first));
                arms.Add(SymTable.Resolve(second));
            }
            else arms.Add(source);
        }
        IReadOnlyList<TypeRef>? common = null;
        foreach (var arm in arms)
        {
            if (AddressedTypes(arm) is not { Count: > 0 } chain) return null;
            common = common is null ? chain : common.Where(chain.Contains).ToArray();
            if (common.Count == 0) return null;
        }
        return common?.FirstOrDefault(t => arms.All(a => Addressed(a, t) is not null)) is { } element ? new ByRefRef(element) : null;
    }

    /// <summary>
    /// φ 入边上的来源。IL 栈合流用的临时变量初值为空，clang 把赋值外提后成为按条件在地址与空之间选择；
    /// 条件已由进入这条边的分支决定时，来源就是决定的一路。
    /// </summary>
    public Sym EdgeSource(PhiSym phi, int edge)
    {
        var source = SymTable.Resolve(phi.Sources[edge]!);
        if (source is not OpSym { Op.Kind: OperatorKind.Select, Args: [var condition, var first, var second] }) return source;
        var (block, next) = (phi.Block.Predecessors[edge], phi.Block);
        for (var steps = 0; steps < 16; steps++)
        {
            if (block.Statements.LastOrDefault() is Branch branch && branch.Target != branch.Fallthrough
                && Implied(values.Operands(branch)[0], branch.Target == next.Start, condition) is { } known)
                return SymTable.Resolve(known ? first : second);
            if (block.Predecessors.Count != 1) break;
            (block, next) = (block.Predecessors[0], block);
        }
        return source;
    }

    /// <summary>已知 known 的真假时 wanted 的真假；只比较同一操作数与常量的有符号比较，不能判定时为 null。</summary>
    private static bool? Implied(Sym known, bool truth, Sym wanted)
    {
        (known, wanted) = (SymTable.Resolve(known), SymTable.Resolve(wanted));
        if (ReferenceEquals(known, wanted)) return truth;
        if (known is not OpSym { Op: { Kind: OperatorKind.Compare, Cond: var held }, Args: [var left, var right] }
            || wanted is not OpSym { Op: { Kind: OperatorKind.Compare, Cond: var asked }, Args: [var other, var bound] }
            || !ReferenceEquals(SymTable.Resolve(left), SymTable.Resolve(other))
            || SymTable.Resolve(right) is not ConstSym a || SymTable.Resolve(bound) is not ConstSym b
            || Interval(held, a.Signed, truth) is not var (low, high)) return null;
        if (Interval(asked, b.Signed, true) is var (trueLow, trueHigh) && low >= trueLow && high <= trueHigh) return true;
        if (Interval(asked, b.Signed, false) is var (falseLow, falseHigh) && low >= falseLow && high <= falseHigh) return false;
        return null;
    }

    /// <summary>有符号比较 x cond c 取值为 truth 时 x 的范围；不是一段区间时为 null。</summary>
    private static (long Low, long High)? Interval(Cond cond, long c, bool truth) => (truth ? cond : cond switch
    {
        Cond.Slt => Cond.Sge, Cond.Sle => Cond.Sgt, Cond.Sgt => Cond.Sle, Cond.Sge => Cond.Slt, Cond.Eq => Cond.Ne, Cond.Ne => Cond.Eq, _ => Cond.FOrdered,
    }) switch
    {
        Cond.Slt when c > long.MinValue => (long.MinValue, c - 1),
        Cond.Sle => (long.MinValue, c),
        Cond.Sgt when c < long.MaxValue => (c + 1, long.MaxValue),
        Cond.Sge => (c, long.MaxValue),
        Cond.Eq => (c, c),
        _ => null,
    };

    /// <summary>值在期望的托管指针类型下是位置的地址时的位置。</summary>
    public Location? AddressArm(Sym value, TypeRef? expected) =>
        expected is ByRefRef { Element: var element } && SymTable.Resolve(value) is var sym
        && (sym is OpSym { Op: { Kind: OperatorKind.Binary, Binary: BinOp.Add } }
            or EntitySym { Symbol.Kind: SymbolKind.StaticFields or SymbolKind.ThreadStaticFields }
            || sym is PhiSym phi && Cursor(phi) is not null) ? Addressed(sym, element) : null;

    /// <summary>地址处类型为 element 的位置；表示链上的外层按字段进入。</summary>
    private Location? Addressed(Sym address, TypeRef element)
    {
        if (Locate(address, StorageBits(element)) is not { Kind: not (LocationKind.Length or LocationKind.StringLength or LocationKind.StringChar) } place) return null;
        if (place.Type.Equals(element)) return place;
        return Inside(place.Type, element) is var (path, inner) ? place with { Path = [.. place.Path, .. path], Type = inner } : null;
    }

    /// <summary>从地址开始的位置类型，由外到内；地址不是位置的起点时为 null。</summary>
    private IReadOnlyList<TypeRef>? AddressedTypes(Sym address)
    {
        var (root, offset, index, scale) = Decompose(address);
        if (root is EntitySym { Symbol: { Kind: SymbolKind.StaticFields or SymbolKind.ThreadStaticFields, Value: TypeRef owner } statics })
            return index is null ? SlotTypes(owner, offset, statics.Kind == SymbolKind.ThreadStaticFields ? SlotKind.ThreadStatic : SlotKind.Static) : null;
        switch (TypeOf(root))
        {
            case ArrayRef array when ElementSize(array.Element) is var size and > 0 && offset >= RuntimeLayout.ArrayData && (index is null || scale % size == 0):
                return ValueTypes(array.Element, (offset - RuntimeLayout.ArrayData) % size);
            case DefinitionRef reference when ManagedTypes.IsReferenceType(reference) && index is null:
                return SlotTypes(reference, offset, SlotKind.Instance);
            case ByRefRef { Element: var element } when index is null:
                return ValueTypes(element, offset);
        }
        return null;
    }

    private enum SlotKind : byte { Instance, Static, ThreadStatic }

    private IReadOnlyList<TypeRef>? SlotTypes(TypeRef owner, long offset, SlotKind kind)
    {
        for (TypeRef? current = owner; current is DefinitionRef d; current = kind == SlotKind.Instance ? d.Definition.BaseType?.Substitute(d.Arguments, []) : null)
        {
            if (types.Layouts.Of(d) is not { } layout) return null;
            foreach (var slot in kind switch { SlotKind.ThreadStatic => layout.ThreadStatics, SlotKind.Static => layout.Statics, _ => layout.Fields })
            {
                var size = ManagedTypes.IsReferenceType(slot.Type) ? 8 : types.Size(slot.Type);
                if (size > 0 && offset >= slot.Offset && offset < slot.Offset + size) return ValueTypes(slot.Type, offset - slot.Offset);
            }
        }
        return null;
    }

    /// <summary>值类型 type 内 offset 字节处开始的位置类型；offset 为零时含自身。</summary>
    private IReadOnlyList<TypeRef>? ValueTypes(TypeRef type, long offset)
    {
        IReadOnlyList<TypeRef>? nested = null;
        if (type is DefinitionRef structure && types.Kind(structure) == TypeKind.Struct && types.Layouts.Of(structure) is { } layout)
            foreach (var field in layout.Fields)
            {
                var at = offset + RuntimeLayout.ObjectHeaderSize - field.Offset;
                if (at < 0 || at >= (ManagedTypes.IsReferenceType(field.Type) ? 8 : types.Size(field.Type))) continue;
                nested = ValueTypes(field.Type, at);
                break;
            }
        return offset == 0 ? [type, .. nested ?? []] : nested;
    }

    /// <summary>
    /// 数组上的指针游标（循环强度削减的逆）：φ 的值恒为 &amp;Array[Index] 再加 Offset - ArrayData 字节。
    /// Index 是合成的 32 位下标 φ，游标上的访问按它写成元素访问，机器指针本身不再出现。
    /// </summary>
    private sealed record ElementCursor(Sym? Array, PhiSym Index, long Offset, int Size);

    private readonly Dictionary<PhiSym, ElementCursor?> cursors = [];
    private readonly Dictionary<(PhiSym, int, long), ElementCursor?> offsetCursors = [];

    private ElementCursor? Cursor(PhiSym phi)
    {
        if (cursors.TryGetValue(phi, out var known)) return known;
        cursors[phi] = null;
        return cursors[phi] = FindCursor(phi, 0);
    }

    /// <summary>
    /// 基址之外单独递推的字节偏移（base + φ）：同样按元素大小 size 的下标解释。start 是第一个元素相对基址的偏移：
    /// 数组为数据区起点，无类型指针缓冲区为 0。
    /// </summary>
    private ElementCursor? OffsetCursor(PhiSym phi, int size, long start = RuntimeLayout.ArrayData)
    {
        if (offsetCursors.TryGetValue((phi, size, start), out var known)) return known;
        offsetCursors[(phi, size, start)] = null;
        return offsetCursors[(phi, size, start)] = size > 0 ? FindCursor(phi, size, start) : null;
    }

    /// <summary>
    /// φ 的每条边是自身加步长，或一个初值：数组上（可带比例下标）或外层游标上的地址；elementSize 不为零时初值没有数组，只是字节偏移。
    /// 步长是元素大小的倍数，各初值落在元素内的同一偏移。
    /// </summary>
    private ElementCursor? FindCursor(PhiSym phi, int elementSize, long start = RuntimeLayout.ArrayData)
    {
        if (phi.Width != 64 || phi.Projection is not null || phi.Sources.Any(s => s is null)) return null;
        var edges = phi.Sources.Select(s => AddressTerms(s!)).ToArray();
        if (!edges.Any(e => ReferenceEquals(e.Root, phi) && e.Index is null && e.Offset != 0)) return null;
        Sym? array = null;
        var size = elementSize;
        long? inside = null;
        var seeds = new (Sym? Index, long Element)?[edges.Length];
        for (var edge = 0; edge < edges.Length; edge++)
        {
            var (root, offset, index, scale) = edges[edge];
            if (ReferenceEquals(root, phi) && index is null) continue;
            if (elementSize != 0)
            {
                if (!ReferenceEquals(root, SymTable.Resolve(phi.Sources[edge]!))) return null;
            }
            else
            {
                if (root is PhiSym outer && index is null && Cursor(outer) is { } nested)
                    (root, offset, index, scale) = (nested.Array!, offset + nested.Offset, nested.Index, nested.Size);
                if (ArrayView(root) is not { } type || ElementSize(type.Element) is not (var bytes and > 0)
                    || array is not null && !ReferenceEquals(array, root)) return null;
                (array, size) = (root, bytes);
            }
            if (offset < start || index is not null && scale != size) return null;
            var within = offset - start;
            if (inside is { } previous && previous != within % size) return null;
            inside = within % size;
            seeds[edge] = (index, within / size);
        }
        if (inside is null || edges.Any(e => ReferenceEquals(e.Root, phi) && e.Index is null && e.Offset % size != 0)) return null;
        var syms = values.Syms;
        var counter = syms.Phi(phi.Block, (phi.Origin, nameof(ElementCursor), size), 32);
        for (var edge = 0; edge < edges.Length; edge++)
        {
            if (seeds[edge] is not { } seed)
            {
                syms.SetSource(counter, edge, syms.Binary(BinOp.Add, counter, syms.Const(unchecked((ulong)(edges[edge].Offset / size)) & Expr.Mask(32), 32), 32));
                continue;
            }
            var first = syms.Const(unchecked((ulong)seed.Element) & Expr.Mask(32), 32);
            if (seed.Index is not { } position) { syms.SetSource(counter, edge, first); continue; }
            var bits = ArrayIndex(position);
            if (bits.Width < 32) return null;
            syms.SetSource(counter, edge, syms.Binary(BinOp.Add, syms.Slice(bits, 0, 32), first, 32));
        }
        return new(array, counter, start + inside.Value, size);
    }
}
