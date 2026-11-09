using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

/// <summary>字段的已证明位来源；Projection 相对于待组成的整体。</summary>
public sealed record ProjectedSym(ValueProjection Projection, Sym Value);

/// <summary>结构体表示计划：优先使用完整读取，否则由非零字段组成，未列出的字段由 initobj 初始化。</summary>
public sealed record AggregatePlan(Sym? Whole, IReadOnlyList<ProjectedSym> Fields)
{
    /// <summary>不为 null 时，值是这次整体读取（快照）改写 Fields 中的直接字段（<see cref="TypeOracle.UpdatedRead"/>）。</summary>
    public Sym? Snapshot { get; init; }
}

public sealed partial class TypeOracle
{
    /// <summary>没有自然结构体类型、按位解释的值；跨字段或非标准宽度的位片、相邻字段合并的读取没有自然类型，同样按位解释。</summary>
    public bool BitRepresentation(Sym value) => SymTable.Resolve(value) is ConcatSym or ConstSym
        || TypeOf(value) is null && (SymTable.Resolve(value) is SliceSym || SymTable.Resolve(value) is ReadSym merged && Parts(merged) is not null
            // 非标准宽度的运算结果不是 IL 标量（按位打包在寄存器里返回的小结构体），只能按位段取用。
            // 选择除外：两路整个值之间的选择（JoinedSelect）按期望的结构体类型选择两路，不拆成位段。
            || SymTable.Resolve(value) is OpSym { Width: not (1 or 8 or 16 or 32 or 64), Op.Kind: not OperatorKind.Select })
        || TypeOf(value) is { } scalar && types.Kind(scalar) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Pointer;

    /// <summary>
    /// 各段都是同一条件下的选择时，拼接就是按该条件在两路拼接之间选择（clang 把结构体值的条件选择拆到每一段上）；不成立时为 null。
    /// </summary>
    public Sym? JoinedSelect(ConcatSym bits)
    {
        Sym? condition = null;
        var (chosen, other) = (new List<Sym>(), new List<Sym>());
        foreach (var part in bits.Parts)
        {
            if (SymTable.Resolve(part) is not OpSym { Op.Kind: OperatorKind.Select, Args: [var test, var yes, var no] }
                || condition is not null && !ReferenceEquals(SymTable.Resolve(test), condition)) return null;
            condition = SymTable.Resolve(test);
            chosen.Add(yes);
            other.Add(no);
        }
        return condition is null ? null : values.Syms.Select(condition, values.Syms.Concat(chosen), values.Syms.Concat(other), bits.Width);
    }

    /// <summary>先证明整体读取，再按共享布局投影字段；只省略已知为零的位，不省略未知或未定义值。</summary>
    public AggregatePlan? Aggregate(Sym bits, DefinitionRef structure)
    {
        if (WholeRead(bits, structure) is { } whole) return new(whole, []);
        if (UpdatedRead(bits, structure) is var (snapshot, changed)) return new(null, changed) { Snapshot = snapshot };
        if (FieldValues(bits, structure) is not { } projected) return null;
        var fields = new List<ProjectedSym>();
        foreach (var (projection, part) in projected)
        {
            if (SymTable.Resolve(part) is ConstSym { Value: 0 }) continue;
            // 一次宽读取的一段正好是内层结构体（q 寄存器复制跨过嵌套结构体）时，同样按叶子取。
            if (projection.Type is DefinitionRef nested && types.Kind(nested) == TypeKind.Struct && (BitRepresentation(part) || SymTable.Resolve(part) is SliceSym { Base: ReadSym }))
            {
                if (Aggregate(part, nested) is not { } inner) return null;
                if (inner.Whole is { } source) fields.Add(new(projection, source));
                else fields.AddRange(inner.Fields.Select(f => new ProjectedSym(f.Projection with
                {
                    Path = [.. projection.Path, .. f.Projection.Path],
                    Bit = projection.Bit + f.Projection.Bit,
                }, f.Value)));
            }
            else fields.Add(new(projection, part));
        }
        return new(null, fields);
    }

    /// <summary>
    /// clang 把结构体局部拆成叶子的 φ（SROA）后按叶子组成：字段都是同一块的 φ 或其片、其中有不可访问的字段时，下降还原成一个结构体 φ。
    /// 给出各字段对应的 φ 与片的低位；不成立时为 null。类型使用分析与下降共用这一判定。
    /// </summary>
    public IReadOnlyList<(ValueProjection Projection, PhiSym Phi, int Low)>? StructPhiLeaves(AggregatePlan plan)
    {
        if (plan.Fields.Count == 0 || !plan.Fields.Any(f => f.Projection.Path.Any(p => !ManagedAccess.Field(types, method, p, p.DeclaringType)))) return null;
        var leaves = new List<(ValueProjection, PhiSym, int)>();
        foreach (var field in plan.Fields)
            switch (SymTable.Resolve(field.Value))
            {
                case PhiSym phi: leaves.Add((field.Projection, phi, 0)); break;
                case SliceSym { Base: var root, Low: var low } when SymTable.Resolve(root) is PhiSym phi: leaves.Add((field.Projection, phi, low)); break;
                default: return null;
            }
        return leaves.All(l => l.Item2.Block == leaves[0].Item2.Block) ? leaves : null;
    }

    /// <summary>结构体 φ 在第 index 条入边上的整个值：各叶子 φ 在这条边上的来源按布局拼接，叶子之间的空位未定义。</summary>
    public Sym? StructPhiEdge(IReadOnlyList<(ValueProjection Projection, PhiSym Phi, int Low)> leaves, DefinitionRef structure, int index)
    {
        var total = types.Size(structure) * 8;
        var parts = new List<Sym>();
        var at = 0;
        foreach (var (projection, phi, low) in leaves.OrderBy(l => l.Projection.Bit))
        {
            if (phi.Sources[index] is not { } source || projection.Bit < at) return null;
            if (projection.Bit > at) parts.Add(values.Syms.Undef(projection.Bit - at));
            parts.Add(values.Syms.Slice(source, low, projection.Width));
            at = projection.Bit + projection.Width;
        }
        if (total <= 0 || at > total) return null;
        if (at < total) parts.Add(values.Syms.Undef(total - at));
        return values.Syms.Concat(parts);
    }

    /// <summary>直接字段的位来源，供值组成与逐字段写入共用。</summary>
    public IReadOnlyList<ProjectedSym>? FieldValues(Sym bits, DefinitionRef structure)
    {
        if (types.Kind(structure) != TypeKind.Struct || types.Layouts.Of(structure) is null) return null;
        var fields = types.Fields(structure).ToArray();
        return fields.Any(p => !p.Fits(bits.Width)) ? null
            : fields.Select(p => new ProjectedSym(p, values.Syms.Slice(bits, p.Bit, p.Width))).ToArray();
    }

    /// <summary>整体位写入可分解的非零叶子；整体读取、快照改写与结构体 φ 仍保留为整体复制。</summary>
    public IReadOnlyList<ValueProjection>? FieldStores(Sym bits, TypeRef type)
    {
        if (type is not DefinitionRef structure || types.Kind(type) != TypeKind.Struct || !BitRepresentation(bits)
            || types.StorageBits(type) > bits.Width || Aggregate(bits, structure) is { } plan && (plan.Whole is not null || plan.Snapshot is not null || StructPhiLeaves(plan) is not null)) return null;
        var leaves = types.Projections(structure).ToArray();
        // 布局未知的叶子（共享泛型字段）没有位范围，整体不能按位分解。
        if (leaves.Any(p => !p.Fits(bits.Width))) return null;
        return leaves.Where(p => SymTable.Resolve(values.Syms.Slice(bits, p.Bit, p.Width)) is not ConstSym { Value: 0 }).ToArray();
    }
}
