using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

/// <summary>字段的已证明位来源；Projection 相对于待组成的整体。</summary>
public sealed record ProjectedSym(ValueProjection Projection, Sym Value);

/// <summary>结构体表示计划：优先使用完整读取，否则由非零字段组成，未列出的字段由 initobj 初始化。</summary>
public sealed record AggregatePlan(Sym? Whole, IReadOnlyList<ProjectedSym> Fields);

public sealed partial class TypeOracle
{
    /// <summary>没有自然结构体类型、按位解释的值。</summary>
    public bool BitRepresentation(Sym value) => SymTable.Resolve(value) is ConcatSym or ConstSym
        || TypeOf(value) is { } natural && types.Kind(natural) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Pointer;

    /// <summary>先证明整体读取，再按共享布局投影字段；只省略已知为零的位，不省略未知或未定义值。</summary>
    public AggregatePlan? Aggregate(Sym bits, DefinitionRef structure)
    {
        if (WholeRead(bits, structure) is { } whole) return new(whole, []);
        if (FieldValues(bits, structure) is not { } projected) return null;
        var fields = new List<ProjectedSym>();
        foreach (var (projection, part) in projected)
        {
            if (SymTable.Resolve(part) is ConstSym { Value: 0 }) continue;
            if (projection.Type is DefinitionRef nested && types.Kind(nested) == TypeKind.Struct && BitRepresentation(part))
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

    /// <summary>直接字段的位来源，供值组成与逐字段写入共用。</summary>
    public IReadOnlyList<ProjectedSym>? FieldValues(Sym bits, DefinitionRef structure)
    {
        if (types.Kind(structure) != TypeKind.Struct || types.Layouts.Of(structure) is null) return null;
        var fields = types.Fields(structure).ToArray();
        return fields.Any(p => !p.Fits(bits.Width)) ? null
            : fields.Select(p => new ProjectedSym(p, values.Syms.Slice(bits, p.Bit, p.Width))).ToArray();
    }

    /// <summary>整体位写入可分解的非零叶子；整体读取仍保留为整体复制。</summary>
    public IReadOnlyList<ValueProjection>? FieldStores(Sym bits, TypeRef type)
    {
        if (type is not DefinitionRef structure || types.Kind(type) != TypeKind.Struct || !BitRepresentation(bits)
            || types.StorageBits(type) > bits.Width || WholeRead(bits, structure) is not null) return null;
        return types.Projections(structure)
            .Where(p => SymTable.Resolve(values.Syms.Slice(bits, p.Bit, p.Width)) is not ConstSym { Value: 0 }).ToArray();
    }
}
