namespace Cpp2CS.Model;

/// <summary>值类型整体内的字段：路径、具体类型与位范围；不包含对象头。</summary>
public sealed record ValueProjection(IReadOnlyList<FieldRef> Path, TypeRef Type, int Bit, int Width)
{
    public bool Contains(int bit, int width) => width > 0 && bit >= Bit && (long)bit + width <= (long)Bit + Width;
    public bool Fits(int width) => Bit >= 0 && Width > 0 && (long)Bit + Width <= width;
}

public sealed partial class ManagedTypes
{
    /// <summary>存储位宽；与结构体不占标量栈位的 ValueWidth 分开。</summary>
    public int StorageBits(TypeRef type) => IsReferenceType(type) || type is ByRefRef or PointerRef ? 64
        : Kind(type) == TypeKind.Struct ? Size(type) * 8 : Math.Max(1, Bits(type));

    /// <summary>直接字段投影，保留嵌套结构体整体。</summary>
    public IEnumerable<ValueProjection> Fields(DefinitionRef structure) => Layouts.Of(structure) is { } layout
        ? layout.Fields.OrderBy(f => f.Offset).Select(f => new ValueProjection([new FieldRef(f.Field, structure)], f.Type,
            (f.Offset - TypeLayout.ObjectHeaderSize) * 8, StorageBits(f.Type))) : [];

    /// <summary>标量叶子投影；嵌套路径和位偏移只在此展开。</summary>
    public IEnumerable<ValueProjection> Projections(DefinitionRef structure)
    {
        foreach (var field in Fields(structure))
            if (field.Type is DefinitionRef inner && Kind(inner) == TypeKind.Struct)
                foreach (var leaf in Projections(inner))
                    yield return leaf with { Path = [.. field.Path, .. leaf.Path], Bit = field.Bit + leaf.Bit };
            else yield return field;
    }

    /// <summary>位范围恰好对应一个字段；不跨字段、不解释填充。布尔最低位可代表整个布尔字段。</summary>
    public ValueProjection? Project(DefinitionRef structure, int bit, int width)
    {
        if (Kind(structure) != TypeKind.Struct || bit < 0 || width <= 0 || (long)bit + width > StorageBits(structure)) return null;
        foreach (var field in Fields(structure))
        {
            if (!field.Contains(bit, width)) continue;
            if (bit == field.Bit && (width == field.Width || width == 1 && Kind(field.Type) == TypeKind.Bool)) return field;
            if (field.Type is DefinitionRef inner && Kind(inner) == TypeKind.Struct && Project(inner, bit - field.Bit, width) is { } leaf)
                return leaf with { Path = [.. field.Path, .. leaf.Path], Bit = field.Bit + leaf.Bit };
        }
        return null;
    }

    /// <summary>已知字段路径的布局证明；不能跨过引用字段进入另一个存储根。</summary>
    public ValueProjection? Project(DefinitionRef structure, IReadOnlyList<FieldRef> path)
    {
        if (Kind(structure) != TypeKind.Struct || path.Count == 0) return null;
        var current = structure;
        var bit = 0;
        for (var i = 0; i < path.Count; i++)
        {
            if (Fields(current).FirstOrDefault(f => f.Path[0].Equals(path[i])) is not { } field) return null;
            bit += field.Bit;
            if (i == path.Count - 1)
            {
                var projection = new ValueProjection(path, field.Type, bit, field.Width);
                return projection.Fits(StorageBits(structure)) ? projection : null;
            }
            if (field.Type is not DefinitionRef nested || Kind(nested) != TypeKind.Struct) return null;
            current = nested;
        }
        return null;
    }

    /// <summary>结构体全部位由互不重叠的整数叶子覆盖，才可按字段打包成整数。</summary>
    public IReadOnlyList<ValueProjection>? IntegerPieces(DefinitionRef structure)
    {
        var fields = Projections(structure).OrderBy(f => f.Bit).ToArray();
        var bit = 0;
        foreach (var field in fields)
        {
            if (Kind(field.Type) is not (TypeKind.Int or TypeKind.Bool) || field.Width <= 0 || field.Bit != bit) return null;
            bit += field.Width;
        }
        return fields.Length > 0 && bit == StorageBits(structure) ? fields : null;
    }
}
