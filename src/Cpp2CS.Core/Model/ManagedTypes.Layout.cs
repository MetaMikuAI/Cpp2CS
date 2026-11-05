namespace Cpp2CS.Model;

public sealed partial class ManagedTypes
{
    /// <summary>托管值的位宽；结构体由字段表达，不使用标量位宽。</summary>
    public int ValueWidth(TypeRef type) => IsReferenceType(type) || type is ByRefRef or PointerRef ? 64
        : Kind(type) == TypeKind.Struct ? 0 : Math.Max(1, Bits(type));

    /// <summary>不含引用的非托管类型：基元，或全部叶子都是基元的值类型，可以被 fixed 固定。</summary>
    public bool Unmanaged(TypeRef type) => Kind(type) switch
    {
        TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double => true,
        TypeKind.Struct => type is DefinitionRef structure && Leaves(structure).ToArray() is { Length: > 0 } leaves && leaves.All(l => Unmanaged(l.Type)),
        _ => false,
    };

    /// <summary>值类型的标量叶子字段：路径、类型与相对值起点的字节偏移。</summary>
    public IEnumerable<(IReadOnlyList<FieldRef> Path, TypeRef Type, int Offset)> Leaves(DefinitionRef structure, int at = 0)
    {
        foreach (var field in Projections(structure)) yield return (field.Path, field.Type, at + field.Bit / 8);
    }

}
